//! The lowering of focused definitions to MLIR text of the `gandr` dialect.
//!
//! A definition that the lowering takes is a thunk in a [`CommandArena`]. Its
//! type is a thunk of a chain of arrows over widths or `Unit` to a returner
//! of a width or of `Unit`.
//! [`lower`] takes each definition of a module, a [`Definition`]. It gives
//! one `tailcc` function for each definition, and its [`Lowered`] prints as
//! one module for `compile`. Each function has the internal linkage, so two
//! objects in one link can each have a definition of one name.
//!
//! The lowering runs one command after the other, with no stack of
//! continuations. A cut against a value binder `μ̃x` names a value and goes on
//! with the body of the binder. A cut against the return continuation ends the
//! function. Thus a body is a straight list of operations.
//!
//! # Items
//!
//! The definition `{force(α) ⇒ ⟨cocase {apply(x; β) ⇒ s} |− α⟩}` is a
//! function with one parameter `x`. Each further `apply` arm adds one
//! parameter, and `β` of the last arm is the return continuation. The commands
//! of `s` become these operations:
//!
//! | Command | Operations |
//! | ------- | ---------- |
//! | `⟨v \|+ β⟩` | `gandr.return` |
//! | `⟨v \|+ μ̃x. s⟩` | none: `x` names `v`, then `s` |
//! | a literal as `v` | `llvm.mlir.constant` |
//! | the unit `()` as `v`, the tuple of no fields | none: the unit has no word |
//! | `⟨w.wrapping_add(v, u) \|+ k⟩` | `gandr.wrapping_add`, then `k`; so for each native row, such as `gandr.not` for `w.not(v)` |
//! | `⟨f \|+ force(apply(v; apply(u; k)))⟩`, `f` the function of a native row | the operation of the row over `v` and `u`, then `k` |
//! | `⟨c \|+ force(apply(v; β))⟩` | `gandr.jump @c` |
//! | `⟨c \|+ force(apply(v; μ̃x. s))⟩` | `gandr.call @c`, `x` its result, then `s` |
//! | `⟨μα. s \|− k⟩`, a naming cut | none: `α` names `k`, then `s`; a cut against `α` is a cut against `k` |
//!
//! A value of `Unit` has no word. So a function of `Unit` has the result
//! `void`, and its `gandr.return` has no operand. A call of it has no result,
//! and its binder names the unit. A parameter of `Unit` is no parameter of the
//! function, and an argument of `Unit` is no operand of a call.
//!
//! The focusing gives a capture `μα` to a bind whose continuation is not a
//! tail, and cuts the capture against that continuation. The capture names
//! the continuation, so it is not a closure.
//!
//! # Boundaries
//!
//! The lowering has no closure. A thunk, a copattern object, or a capture `μα`
//! that is not the producer of a cut, gives [`Form::Closure`]. A negative cut
//! of a capture against a binder `μ̃` binds the capture by name, so it is a
//! closure too, and gives [`Form::Closure`].
//!
//! The elaboration gives a native row in a body as the row's own function, a
//! thunk `thunk(cocase{apply(x; β) ⇒ … ⟨row(x, …) |+ β⟩})`, which `force` and
//! the `apply` frames of the arguments open. Such a thunk against `force` is
//! the operation of the row, with no closure. A thunk of another shape against
//! `force` gives [`Form::Closure`].
//!
//! A case of an injection takes its arm with no step. A case of a sum switches
//! on its tag to one block for each arm. A branch that delivers to a consumer
//! after its case branches to the join of that consumer: a block of the
//! function with one argument, which the branches of the case share. An
//! injection to a join gives [`Form::Sum`]. A call has each parameter of
//! its callee, so a partial application gives [`Form::Delivery`]. A tuple or a
//! product with a component gives [`Form::Product`]. A sum with another
//! layout gives [`Form::Sum`]. The sum of no summands, `Void`, has no value.
//! So a function of `Void` has no result, as one of `Unit`. A call of `Void`
//! that is not a jump ends its block with `llvm.unreachable`, and the command
//! after it gives no step. A parameter of `Void` gives [`Form::Signature`].
//!
//! A recursive thunk at the head of a definition is the function of the
//! definition. Its self binder names that function. Thus a call of itself in
//! a tail is `gandr.jump`, and a loop uses no stack. A call of itself that is
//! not in a tail is `gandr.call`. Such a call runs with a stack. A recursive
//! thunk elsewhere in a body gives [`Form::Fixpoint`]. The self binder as a
//! value gives [`Form::Closure`].
//!
//! The lowering does not check types. The verifier of the dialect refuses a
//! wrong operand, a wrong return type or a wrong callee by name.
//!
//! A node or a type that the lowering has no form for, such as a `perform`, a
//! list or a record, gives [`Form::Outside`] with the name of its variant.
//! The lowering reads the nodes of a body and not the effect row of its
//! returner, so a definition whose row is not empty lowers when each node of
//! its body has a form. A native row lowers by its typed operation:
//! `Primitive::machine_operation`, or `Primitive::checked_operation` for a
//! `checked_` row.
//!
//! # References
//!
//! - `vault:01a21222-e4bd-74a7-82be-989aaccefe85` — dependency: § seam-forms,
//!   the answer of the lowering for each node, and § seam-changes-library.
//! - `vault:01a213f1-00b9-7420-9fb8-79fcb9e4fc03` — dependency: § seam-open,
//!   the five rules by which the lowering reads the trunk.

use core::fmt;

use anodized::spec;
use gandr_core_sequent::CommandArena;
use gandr_core_sequent::CommandId;
use gandr_core_sequent::CommandNode;
use gandr_core_sequent::ConstructorTag;
use gandr_core_sequent::ConsumerId;
use gandr_core_sequent::ConsumerNode;
use gandr_core_sequent::CopatternArm;
use gandr_core_sequent::CovariableIndex;
use gandr_core_sequent::DestructorTag;
use gandr_core_sequent::PatternArm;
use gandr_core_sequent::ProducerId;
use gandr_core_sequent::ProducerNode;
use gandr_core_term::CompType;
use gandr_core_term::CoreArena;
use gandr_core_term::ValueType;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_core_term::primitive::Arguments;
use gandr_core_term::primitive::CheckedInstruction;
use gandr_core_term::primitive::MachineInstruction;
use gandr_core_term::primitive::Primitive;
use gandr_core_term::primitive::PrimitiveType;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::FixedInteger;
use gandr_kernel_term::IntegerWidth;
use gandr_kernel_term::Literal;
use gandr_kernel_term::Summand;
use gandr_theory_cell_complexes::Polarity;

use crate::entry::Entry;

/// The name of a definition as an MLIR symbol, such as `inc`.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Symbol<'name>(&'name str);

impl<'name> From<&'name str> for Symbol<'name>
{
    /// The text as the name of a symbol.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(name: &'name str) -> Self
    {
        Self(name)
    }
}

impl fmt::Display for Symbol<'_>
{
    /// The text of the name.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(self.0)
    }
}

/// Whether `name` is a bare identifier of MLIR: a letter or `_`, then letters,
/// digits, `_`, `$` and `.`.
///
/// # Specification
/// - ensures: true exactly when the name is not empty, its first character is
///   an ASCII letter or `_`, and each other character is an ASCII letter, an
///   ASCII digit, `_`, `$` or `.`.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the names of the fixture are bare identifiers, and a name
///   with a space is refused.
/// - witness: `lower::tests::each_definition_of_the_fixture_becomes_an_object`
/// - witness: `lower::tests::a_name_that_is_no_identifier_is_refused`
#[spec(ensures: |ret| ret.0 == (!name.0.is_empty() && !name.0.starts_with(|first: char| first.is_ascii_digit() || first == '$' || first == '.')
    && name.0.chars().all(|character| character.is_ascii_alphanumeric() || matches!(character, '_' | '$' | '.'))))]
fn bare(name: Symbol<'_>) -> Bare
{
    let mut characters = name.0.chars();
    let head = characters
        .next()
        .is_some_and(|first| first.is_ascii_alphabetic() || first == '_');
    Bare(
        head && characters.all(|character| {
            character.is_ascii_alphanumeric() || matches!(character, '_' | '$' | '.')
        }),
    )
}

/// Whether a name is a bare identifier of MLIR.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Bare(bool);

/// Refuse `name` when it is not a bare identifier of MLIR.
///
/// # Specification
/// - ensures: `Ok` exactly when [`bare`] holds for `name`.
/// - fails: [`Form::Symbol`] for a name that is not a bare identifier.
/// - panics: none.
///
/// # Errors
///
/// As the failure clause states.
///
/// # Adequacy
/// - hypothesis: L3 — the name of an export with a space is refused.
/// - witness: `lower::tests::an_export_outside_the_fragment_is_refused`
#[spec(ensures: |ret| ret.is_ok() == (bare(name) == Bare(true)))]
pub fn named(name: Symbol<'_>) -> Result<(), Form>
{
    if bare(name) == Bare(false) {
        return Err(Form::Symbol);
    }
    Ok(())
}

/// One definition of a module, at its admission position in the definitions
/// that [`lower`] takes.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Definition<'name>
{
    /// The name of its function.
    pub name: Symbol<'name>,
    /// Its focused value, a thunk in the command arena.
    pub value: ProducerId,
    /// The type of its value in the core arena: a thunk of a chain of arrows
    /// over widths or `Unit` to a returner of a width or of `Unit`.
    pub signature: ValueTypeId,
}

/// A command the lowering does not lay out.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Form
{
    /// A node or a type the arenas do not hold.
    Dangling,
    /// A variable bound by nothing in the command, a covariable other than
    /// the return continuation, or a constant with no definition.
    Unbound,
    /// A destructor whose children contradict its tag.
    Destructor,
    /// A delivery its consumer does not take: a value that is not a word where
    /// a word goes, a call with a count of arguments other than the parameters
    /// of its callee, or a call against a frame that is not a binder and not
    /// the return continuation.
    Delivery,
    /// A thunk, a copattern object or a capture inside a body. The lowering
    /// has no closure.
    Closure,
    /// A type that is not a thunk of arrows over widths to a returner of a
    /// width, or a value that does not open one `apply` arm for each arrow.
    Signature,
    /// A native row that the dialect has no operation for.
    Native,
    /// A name that is not a bare identifier of MLIR.
    Symbol,
    /// A tuple or a product with a component. The lowering has no layout for
    /// it.
    Product,
    /// An injection into an injection, a sum that is not of two summands of a
    /// word or `Unit`, a case of a value that is not a sum, or an injection or
    /// a case where a word goes. The lowering lays out no other sum, and no
    /// constructor of a data type or data case.
    Sum,
    /// A recursive thunk, the image of a fixpoint, that is not the body of a
    /// definition. Such a fixpoint is a closure, and the lowering has no
    /// closure.
    Fixpoint,
    /// A node or a type that the lowering has no form for, by the name of its
    /// variant, such as `CommandNode::Perform` or `ValueType::Record`.
    Outside(&'static str),
}

impl fmt::Display for Form
{
    /// Names the form.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(match *self {
            Self::Dangling => "a node the arena does not hold",
            Self::Unbound => "a variable bound by nothing in the command",
            Self::Destructor => "a destructor whose children contradict its tag",
            Self::Delivery => "a delivery of a value its consumer does not take",
            Self::Closure => "a closure inside a body",
            Self::Signature => "a definition that is not a function of words",
            Self::Native => "a native row with no operation of the dialect",
            Self::Symbol => "a name that is not an identifier of MLIR",
            Self::Product => "a tuple or a product with a component",
            Self::Sum => "an injection or a case with no layout",
            Self::Fixpoint => "a fixpoint inside a body",
            Self::Outside(node) => {
                return write!(f, "`{node}`, which the lowering has no form for");
            },
        })
    }
}

impl core::error::Error for Form
{
}

/// A value of a function: a parameter or the result of an operation, printed
/// as `%v<number>`.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Value(usize);

impl fmt::Display for Value
{
    /// The name of the value.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        write!(f, "%v{}", self.0)
    }
}

/// The MLIR type of a width: a signless integer of its bit count.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Word(IntegerWidth);

impl fmt::Display for Word
{
    /// The type, such as `i8`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        write!(f, "i{}", u32::from(self.0.bits()))
    }
}

/// The MLIR form of a value type: a word, no word for `Unit`, the two words of
/// a sum, or no value for `Void`.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Kind
{
    /// A word of this width.
    Word(IntegerWidth),
    /// The type `Unit`, which has no word.
    Unit,
    /// A sum of two summands, in the layout [`SUM`].
    Sum(SumLayout),
    /// The sum of no summands, which has no value: a call of it does not
    /// return.
    Void,
}

impl Kind
{
    /// The MLIR type of a value of this kind, or `None` for `Unit` and `Void`.
    ///
    /// # Specification
    /// trivial.
    const fn typed(self) -> Option<Typed>
    {
        match self {
            Self::Word(width) => Some(Typed::Word(width)),
            Self::Unit | Self::Void => None,
            Self::Sum(layout) => Some(Typed::Sum(layout)),
        }
    }
}

/// The field of one summand of a sum: a word, or no word for `Unit`.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Field
{
    /// A word of this width.
    Word(IntegerWidth),
    /// The type `Unit`, whose field holds 0.
    Unit,
}

/// The field of each summand of a sum of two summands, the first summand
/// first.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct SumLayout([Field; 2]);

/// The MLIR type of a sum: the tag word, which holds the position of the
/// summand, then the field word, which holds the field of that summand.
const SUM: &str = "!llvm.struct<(i64, i64)>";

/// A value that a body delivers: a word, the unit, which has no word, a sum
/// in its two words, or an injection that has no words yet.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Operand
{
    /// The word of this value.
    Word(Value),
    /// The unit.
    Unit,
    /// A sum in the layout [`SUM`].
    Sum(Value),
    /// An injection whose words no step wrote: a case of it takes its branch
    /// with no step, and a call or a return writes its words.
    Injected
    {
        /// The summand.
        summand: Summand,
        /// The field: the word of the summand, or the unit.
        field: Payload,
    },
}

/// The field of an injection: a word, or the unit, which has no word.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Payload
{
    /// The word of this value.
    Word(Value),
    /// The unit.
    Unit,
}

/// The MLIR type of a value of a function: a word, or a sum.
#[derive(Clone, Debug, Eq, PartialEq)]
enum Typed
{
    /// A word of this width.
    Word(IntegerWidth),
    /// A sum in the layout [`SUM`], with the field of each summand.
    Sum(SumLayout),
}

impl fmt::Display for Typed
{
    /// The type, such as `i8` or `!llvm.struct<(i64, i64)>`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            Self::Word(width) => write!(f, "{}", Word(width)),
            Self::Sum(_) => f.write_str(SUM),
        }
    }
}

/// A native operation of a width in the dialect.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Operation
{
    /// `gandr.wrapping_add`.
    WrappingAdd,
    /// `gandr.wrapping_sub`.
    WrappingSub,
    /// `gandr.wrapping_mul`.
    WrappingMul,
    /// `gandr.and`.
    And,
    /// `gandr.or`.
    Or,
    /// `gandr.xor`.
    Xor,
    /// `gandr.not`.
    Not,
}

impl fmt::Display for Operation
{
    /// Writes the name of the operation in the dialect, after `gandr.`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(match *self {
            Self::WrappingAdd => "wrapping_add",
            Self::WrappingSub => "wrapping_sub",
            Self::WrappingMul => "wrapping_mul",
            Self::And => "and",
            Self::Or => "or",
            Self::Xor => "xor",
            Self::Not => "not",
        })
    }
}

/// A `checked_` row of a width: an operation whose answer is the sum of the
/// width and `Unit`, with the absence on the right.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Checked
{
    /// `checked_add`: absent when the sum leaves the width.
    Add,
    /// `checked_sub`: absent when the difference leaves the width.
    Sub,
    /// `checked_mul`: absent when the product leaves the width.
    Mul,
    /// `checked_shl`: absent when the amount is not below the bit count.
    Shl,
    /// `checked_shr`: absent when the amount is not below the bit count. A
    /// signed width shifts in its sign.
    Shr,
}

/// The operation of a native row: a word, or a `checked_` sum.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Native
{
    /// A row whose answer is a word.
    Word(Operation),
    /// A row whose answer is a sum of the width and `Unit`.
    Checked(Checked),
}

/// Whether a width is signed: `i8`, `i16`, `i32`, `i64` and `isize`.
///
/// # Specification
/// trivial.
const fn signed(width: IntegerWidth) -> Signed
{
    Signed(matches!(
        width,
        IntegerWidth::I8
            | IntegerWidth::I16
            | IntegerWidth::I32
            | IntegerWidth::I64
            | IntegerWidth::Isize
    ))
}

/// Whether a width is signed.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Signed(bool);

/// One operation of a function.
#[derive(Clone, Debug, Eq, PartialEq)]
enum Step<'name>
{
    /// `value = llvm.mlir.constant(literal)`.
    Constant
    {
        /// The result.
        value: Value,
        /// The literal.
        literal: FixedInteger,
    },
    /// `value = gandr.<operation> operands`.
    Native
    {
        /// The result.
        value: Value,
        /// The operation.
        operation: Operation,
        /// The operands, in the order of the row.
        operands: Arguments<Value>,
    },
    /// `value = gandr.call @callee(operands)`, or `gandr.call` with no result
    /// for a callee of `Unit`.
    Call
    {
        /// The result, or `None` for a callee of `Unit`.
        value: Option<Value>,
        /// The callee.
        callee: Symbol<'name>,
        /// The first operand in the operands of the function.
        start: OperandIndex,
        /// One past the last operand.
        end: OperandIndex,
    },
    /// `gandr.jump @callee(operands)`.
    Jump
    {
        /// The callee.
        callee: Symbol<'name>,
        /// The first operand in the operands of the function.
        start: OperandIndex,
        /// One past the last operand.
        end: OperandIndex,
    },
    /// `gandr.return value`, or `gandr.return` with no value for the unit.
    Return(Option<Value>),
    /// The answer of a `checked_` row of `width` in the layout [`SUM`]: the
    /// tag 1 when the answer is absent, and otherwise the tag 0 with the
    /// answer in the field. The step prints several operations, whose names
    /// extend the name of `value`.
    Checked
    {
        /// The sum.
        value: Value,
        /// The row.
        operation: Checked,
        /// The width of the operands.
        width: IntegerWidth,
        /// The two operands, the left one first.
        operands: [Value; 2],
    },
    /// `value = llvm.mlir.undef`: a sum whose words no step wrote yet.
    Undef
    {
        /// The result.
        value: Value,
    },
    /// `value = llvm.insertvalue word, sum[place]`.
    Insert
    {
        /// The result.
        value: Value,
        /// The sum before the step.
        sum: Value,
        /// The word that the step writes.
        word: Value,
        /// The word of the sum that the step writes.
        place: SumWord,
    },
    /// `value = llvm.extractvalue sum[place]`.
    Extract
    {
        /// The result.
        value: Value,
        /// The sum.
        sum: Value,
        /// The word of the sum that the step reads.
        place: SumWord,
    },
    /// `value = llvm.zext word`: the field word of a narrower word.
    Widen
    {
        /// The result, of 64 bits.
        value: Value,
        /// The narrower word.
        word: Value,
    },
    /// `value = llvm.trunc word`: a narrower word of the field word.
    Narrow
    {
        /// The result.
        value: Value,
        /// The field word, of 64 bits.
        word: Value,
    },
    /// `llvm.switch tag, second [0: first]`: the branch of the first summand
    /// when the tag is 0, and the branch of the second summand otherwise.
    Switch
    {
        /// The tag word of the sum.
        tag: Value,
        /// The block of the first summand.
        first: Block,
        /// The block of the second summand.
        second: Block,
    },
    /// `llvm.br ^bb<n>(operand)`: the end of a branch that delivers to the
    /// join of a continuation outside its case.
    Branch
    {
        /// The block of the join.
        block: Block,
        /// The operand that the join receives, or `None` for the unit.
        operand: Option<Value>,
    },
    /// `^bb<n>(argument):`: the start of a block of the function.
    Label
    {
        /// The block.
        block: Block,
        /// The argument of the block, or `None`.
        argument: Option<Value>,
    },
    /// `llvm.unreachable`: the end of a block after a call that does not
    /// return.
    Unreachable,
}

/// A word of a sum in the layout [`SUM`].
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum SumWord
{
    /// The tag word, at place 0.
    Tag,
    /// The field word, at place 1.
    Field,
}

impl fmt::Display for SumWord
{
    /// The place, `0` or `1`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(match *self {
            Self::Tag => "0",
            Self::Field => "1",
        })
    }
}

/// A block of a function after its first block, printed as `^bb<number>`.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Block(usize);

impl fmt::Display for Block
{
    /// The name of the block.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        write!(f, "^bb{}", self.0)
    }
}

/// A place in the operands of a function.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct OperandIndex(usize);

/// The parameters and the result of a function.
#[derive(Clone, Debug, Eq, PartialEq)]
struct Signature
{
    /// The kind of each parameter, the first one first.
    parameters: Box<[Kind]>,
    /// The kind of the result.
    result: Kind,
}

/// One function of a module.
#[derive(Clone, Debug, Eq, PartialEq)]
struct Function<'name>
{
    /// The admission position of its definition.
    constant: ConstantIndex,
    /// The name of the function.
    name: Symbol<'name>,
    /// The parameters and the result.
    signature: Signature,
    /// The type of each value. The first values are the parameters that have
    /// a word or a sum.
    types: Vec<Typed>,
    /// The operands of each call, each jump and each operation of a machine
    /// body, one run for each.
    operands: Vec<Value>,
    /// The operations, in the order of the run, with the label of each block
    /// before the operations of the block.
    steps: Vec<Step<'name>>,
    /// The count of the blocks after the first block.
    blocks: usize,
}

/// The functions of each definition, which print as one MLIR module of the
/// `llvm` and `gandr` dialects.
///
/// # Specification
/// - ensures: one function for each definition, in the order of the admission
///   positions. Each function ends with `gandr.return` or `gandr.jump`.
/// - panics: none.
/// - executable: none — a type-level block: a data declaration has no body and
///   no call boundary to check.
///
/// # Adequacy
/// - hypothesis: L3 — the module of the fixture compiles to an ELF object with
///   a symbol for each definition, and its text has the operations of the table
///   of the module.
/// - witness: `lower::tests::each_definition_of_the_fixture_becomes_an_object`
/// - witness: `lower::tests::twice_calls_inc_and_jumps_to_inc`
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Lowered<'name>
{
    /// One function for each definition, in the order of the admission
    /// positions. A member of a block has no function.
    functions: Vec<Function<'name>>,
}

impl fmt::Display for Lowered<'_>
{
    /// The module as MLIR text, one `llvm.func internal tailcc` for each
    /// function.
    ///
    /// # Specification
    /// - ensures: each function prints as its name, its parameters `%v0` and
    ///   on, its result type, and one line for each step.
    /// - fails: an error of `f`.
    /// - panics: none.
    /// - executable: none — a clause over the written text would print the
    ///   module a second time.
    ///
    /// # Errors
    ///
    /// An error of the formatter.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the text of the fixture compiles, and the literal
    ///   `255u8` prints as its pattern `-1 : i8`.
    /// - witness: `lower::tests::each_definition_of_the_fixture_becomes_an_object`
    /// - witness: `lower::tests::wrapped_gives_the_pattern_of_the_greatest_byte`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        for function in &self.functions {
            write!(f, "llvm.func internal tailcc @{}(", function.name.0)?;
            let typed = function
                .signature
                .parameters
                .iter()
                .filter_map(|&kind| kind.typed());
            for (place, ty) in typed.enumerate() {
                if place > 0 {
                    f.write_str(", ")?;
                }
                write!(f, "{}: {ty}", Value(place))?;
            }
            match function.signature.result.typed() {
                Some(ty) => writeln!(f, ") -> {ty} {{")?,
                None => f.write_str(") {\n")?,
            }
            for step in &function.steps {
                Self::step(f, function, step)?;
            }
            f.write_str("}\n")?;
        }
        Ok(())
    }
}

impl Lowered<'_>
{
    /// Print one step of `function` as one line.
    ///
    /// # Specification
    /// - ensures: the line of the operation of `step`, with the type of each
    ///   value from the types of `function`.
    /// - fails: an error of `f`, or a value or an operand run that the function
    ///   does not hold.
    /// - panics: none.
    /// - executable: none — a clause over the written text would print the line
    ///   a second time.
    ///
    /// # Errors
    ///
    /// An error of the formatter, also for a step that names a value or an
    /// operand run outside the function. The lowering makes no such step.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each kind of step is in the text of the fixture,
    ///   which compiles.
    /// - witness: `lower::tests::each_definition_of_the_fixture_becomes_an_object`
    /// - witness: `lower::tests::twice_calls_inc_and_jumps_to_inc`
    fn step(
        f: &mut fmt::Formatter<'_>,
        function: &Function<'_>,
        step: &Step<'_>,
    ) -> fmt::Result
    {
        let word = |value: Value| function.types.get(value.0).ok_or(fmt::Error);
        match *step {
            Step::Constant { value, literal } => {
                writeln!(
                    f,
                    "  {value} = llvm.mlir.constant({} : {ty}) : {ty}",
                    Pattern(literal),
                    ty = word(value)?
                )
            },
            Step::Native {
                value,
                operation,
                operands,
            } => {
                write!(f, "  {value} = gandr.{operation} ")?;
                Self::list(f, &operands, Ok)?;
                writeln!(f, " : {}", word(value)?)
            },
            Step::Call {
                value,
                callee,
                start,
                end,
            } => {
                let operands = function.operands.get(start.0 .. end.0).ok_or(fmt::Error)?;
                f.write_str("  ")?;
                if let Some(value) = value {
                    write!(f, "{value} = ")?;
                }
                write!(f, "gandr.call @{callee}(")?;
                Self::list(f, operands, Ok)?;
                f.write_str(") : (")?;
                Self::list(f, operands, word)?;
                match value {
                    Some(value) => writeln!(f, ") -> {}", word(value)?),
                    None => f.write_str(") -> ()\n"),
                }
            },
            Step::Jump { callee, start, end } => {
                let operands = function.operands.get(start.0 .. end.0).ok_or(fmt::Error)?;
                write!(f, "  gandr.jump @{callee}(")?;
                Self::list(f, operands, Ok)?;
                if operands.is_empty() {
                    return f.write_str(")\n");
                }
                f.write_str(") : (")?;
                Self::list(f, operands, word)?;
                f.write_str(")\n")
            },
            Step::Return(Some(value)) => {
                writeln!(f, "  gandr.return {value} : {}", word(value)?)
            },
            Step::Return(None) => f.write_str("  gandr.return\n"),
            Step::Unreachable => f.write_str("  llvm.unreachable\n"),
            Step::Checked {
                value,
                operation,
                width,
                operands,
            } => Self::checked(f, value, (operation, width), operands),
            Step::Undef { value } => writeln!(f, "  {value} = llvm.mlir.undef : {SUM}"),
            Step::Insert {
                value,
                sum,
                word: inserted,
                place,
            } => writeln!(
                f,
                "  {value} = llvm.insertvalue {inserted}, {sum}[{place}] : {SUM}"
            ),
            Step::Extract { value, sum, place } => {
                writeln!(f, "  {value} = llvm.extractvalue {sum}[{place}] : {SUM}")
            },
            Step::Widen {
                value,
                word: narrow,
            } => writeln!(
                f,
                "  {value} = llvm.zext {narrow} : {} to i64",
                word(narrow)?
            ),
            Step::Narrow { value, word: wide } => {
                writeln!(f, "  {value} = llvm.trunc {wide} : i64 to {}", word(value)?)
            },
            Step::Switch { tag, first, second } => {
                writeln!(
                    f,
                    "  llvm.switch {tag} : i64, {second} [\n    0: {first}\n  ]"
                )
            },
            Step::Branch {
                block,
                operand: None,
            } => writeln!(f, "  llvm.br {block}"),
            Step::Branch {
                block,
                operand: Some(operand),
            } => {
                writeln!(f, "  llvm.br {block}({operand} : {})", word(operand)?)
            },
            Step::Label {
                block,
                argument: None,
            } => writeln!(f, "{block}:"),
            Step::Label {
                block,
                argument: Some(argument),
            } => {
                writeln!(f, "{block}({argument}: {}):", word(argument)?)
            },
        }
    }

    /// Print the operations of a `checked_` row: the answer and its absence
    /// in the width, then the sum in the layout [`SUM`]. The field of an
    /// absent answer holds 0, as [`Field::Unit`] states.
    ///
    /// # Specification
    /// - ensures: the text of an addition, a subtraction or a product with
    ///   overflow of the LLVM dialect, or of a shift whose amount is below the
    ///   bit count, then the sum `value`.
    /// - fails: an error of `f`.
    /// - panics: none.
    /// - executable: none — a clause over the written text would print the
    ///   operations a second time.
    ///
    /// # Errors
    ///
    /// An error of the formatter.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each `checked_` row of each width lowers to text that
    ///   compiles, and its two branches run. On each pair of edge operands, the
    ///   compiled answer is the answer of the evaluator, in its summand and in
    ///   each bit of its word.
    /// - witness: `lower::tests::each_row_of_the_native_table_becomes_an_object`
    /// - witness: `lower::tests::each_branch_of_a_checked_row_runs`
    /// - witness: `lower::tests::the_compiled_answer_of_each_row_is_the_answer_of_the_evaluator`
    ///
    /// # Cost
    /// O(1) writes.
    fn checked(
        f: &mut fmt::Formatter<'_>,
        value: Value,
        (operation, width): (Checked, IntegerWidth),
        [left, right]: [Value; 2],
    ) -> fmt::Result
    {
        let bits = u32::from(width.bits());
        let signed = signed(width).0;
        let name = match operation {
            Checked::Add => "add",
            Checked::Sub => "sub",
            Checked::Mul => "mul",
            Checked::Shl => "shl",
            Checked::Shr if signed => "ashr",
            Checked::Shr => "lshr",
        };
        if matches!(operation, Checked::Shl | Checked::Shr) {
            writeln!(
                f,
                "  {value}_n = llvm.mlir.constant({bits} : i{bits}) : i{bits}"
            )?;
            writeln!(
                f,
                "  {value}_o = llvm.icmp \"uge\" {right}, {value}_n : i{bits}"
            )?;
            writeln!(f, "  {value}_z = llvm.mlir.constant(0 : i{bits}) : i{bits}")?;
            writeln!(
                f,
                "  {value}_a = llvm.select {value}_o, {value}_z, {right} : i1, i{bits}"
            )?;
            writeln!(f, "  {value}_w = llvm.{name} {left}, {value}_a : i{bits}")?;
        }
        else {
            let sign = if signed { "s" } else { "u" };
            writeln!(
                f,
                "  {value}_r = \"llvm.intr.{sign}{name}.with.overflow\"({left}, {right}) : (i{bits}, i{bits}) -> !llvm.struct<(i{bits}, i1)>"
            )?;
            writeln!(
                f,
                "  {value}_w = llvm.extractvalue {value}_r[0] : !llvm.struct<(i{bits}, i1)>"
            )?;
            writeln!(
                f,
                "  {value}_o = llvm.extractvalue {value}_r[1] : !llvm.struct<(i{bits}, i1)>"
            )?;
        }
        writeln!(f, "  {value}_t = llvm.zext {value}_o : i1 to i64")?;
        let field = if bits == 64 { "w" } else { "f" };
        if bits != 64 {
            writeln!(f, "  {value}_f = llvm.zext {value}_w : i{bits} to i64")?;
        }
        writeln!(f, "  {value}_k = llvm.mlir.constant(0 : i64) : i64")?;
        writeln!(
            f,
            "  {value}_g = llvm.select {value}_o, {value}_k, {value}_{field} : i1, i64"
        )?;
        writeln!(f, "  {value}_u = llvm.mlir.undef : {SUM}")?;
        writeln!(
            f,
            "  {value}_s = llvm.insertvalue {value}_t, {value}_u[0] : {SUM}"
        )?;
        writeln!(
            f,
            "  {value} = llvm.insertvalue {value}_g, {value}_s[1] : {SUM}"
        )
    }

    /// Print the text of `item` for each operand, separated by `, `.
    ///
    /// # Specification
    /// - ensures: the text of each operand of `operands`, in order.
    /// - fails: an error of `f` or of `item`.
    /// - panics: none.
    /// - executable: none — a clause over the written text would print the list
    ///   a second time.
    ///
    /// # Errors
    ///
    /// An error of the formatter or of `item`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the call and the jump of `twice` print their operand
    ///   and its type, and the text compiles.
    /// - witness: `lower::tests::twice_calls_inc_and_jumps_to_inc`
    fn list<Item, Text>(
        f: &mut fmt::Formatter<'_>,
        operands: &[Value],
        item: Item,
    ) -> fmt::Result
    where
        Item: Fn(Value) -> Result<Text, fmt::Error>,
        Text: fmt::Display,
    {
        for (place, &operand) in operands.iter().enumerate() {
            if place > 0 {
                f.write_str(", ")?;
            }
            write!(f, "{}", item(operand)?)?;
        }
        Ok(())
    }
}

impl<'name> Lowered<'name>
{
    /// The entry of a program whose main definition is at `main`, with the
    /// machine block of exit.
    ///
    /// # Errors
    ///
    /// [`Form::Unbound`] when the module has no function at `main`, and
    /// [`Form::Signature`] when that function takes a parameter.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: an [`Entry`] that names the function at `main` and the width
    ///   of its result, when that function takes no parameter and gives a word.
    /// - fails: with [`Form::Unbound`] past the functions of the module; with
    ///   [`Form::Signature`] for a function with a parameter or of `Unit`.
    /// - executable: none — the fields of an entry are private to its module.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — `main` of the fixture gives an entry that links and
    ///   exits with its answer; `inc` has a parameter, and a position past the
    ///   module names no function.
    /// - witness: `lower::tests::an_object_with_the_entry_links_and_exits_with_the_answer`
    /// - witness: `lower::tests::an_entry_needs_a_function_with_no_parameter`
    #[inline]
    pub fn entry(
        &self,
        main: ConstantIndex,
    ) -> Result<Entry<'name>, Form>
    {
        let function = self
            .functions
            .iter()
            .find(|function| function.constant == main)
            .ok_or(Form::Unbound)?;
        let (true, Kind::Word(width)) = (
            function.signature.parameters.is_empty(),
            function.signature.result,
        )
        else {
            return Err(Form::Signature);
        };
        Ok(Entry::new(function.name, width))
    }
}

/// A literal as the value of an MLIR integer attribute: its bit pattern read
/// as a signed integer of its width, so that `255u8` is `-1`.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Pattern(FixedInteger);

impl fmt::Display for Pattern
{
    /// The signed value of the pattern.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        let signed = match self.0 {
            FixedInteger::U8(value) => i64::from(value.cast_signed()),
            FixedInteger::I8(value) => i64::from(value),
            FixedInteger::U16(value) => i64::from(value.cast_signed()),
            FixedInteger::I16(value) => i64::from(value),
            FixedInteger::U32(value) => i64::from(value.cast_signed()),
            FixedInteger::I32(value) => i64::from(value),
            FixedInteger::U64(value) | FixedInteger::Usize(value) => value.cast_signed(),
            FixedInteger::I64(value) | FixedInteger::Isize(value) => value,
        };
        write!(f, "{signed}")
    }
}

/// The kind of a value type: a word, no word for `Unit`, a sum, or no value
/// for `Void`.
///
/// # Specification
/// - ensures: the width of a base type of a width, [`Kind::Unit`] for the type
///   `Unit`, the field of each summand for a sum of two summands, each a width
///   or `Unit`, and [`Kind::Void`] for the sum of no summands.
/// - fails: [`Form::Dangling`] for a type the arena does not hold,
///   [`Form::Signature`] for a thunk type, a data type, a universe or a decode,
///   [`Form::Product`] for a product with a component, and [`Form::Sum`] for a
///   sum of another count of summands or with a summand that is not a width or
///   `Unit`.
/// - panics: none.
///
/// # Errors
///
/// As the failure clause states.
///
/// # Adequacy
/// - hypothesis: L3 — the `u8` types of the fixture give `i8`, `Unit` gives no
///   word, `u8 + Unit` and `Unit + Unit` give their fields, `Void` gives no
///   value, and a thunk parameter, a product of one component and a sum of
///   three summands are refused.
/// - witness: `lower::tests::each_definition_of_the_fixture_becomes_an_object`
/// - witness: `lower::tests::a_definition_of_unit_returns_no_value`
/// - witness: `lower::tests::a_thunk_parameter_is_refused`
/// - witness: `lower::tests::a_tuple_or_a_product_with_a_component_is_refused_by_name`
/// - witness: `lower::tests::each_branch_of_each_case_runs_and_exits_with_its_answer`
/// - witness: `lower::tests::a_sum_with_no_layout_is_refused_by_name`
#[spec(ensures: |ret| ret.is_err() || types.value_type(word).is_some_and(|ty| matches!(*ty, ValueType::Base(_) | ValueType::Product(_) | ValueType::Sum(_))))]
fn kind(
    types: &CoreArena,
    word: ValueTypeId,
) -> Result<Kind, Form>
{
    // A summand is a word or `Unit`. Each other type that the lowering lays
    // out, or refuses as a signature, has no layout as a summand.
    let field = |summand: ValueTypeId| match kind(types, summand) {
        Ok(Kind::Word(width)) => Ok(Field::Word(width)),
        Ok(Kind::Unit) => Ok(Field::Unit),
        Ok(Kind::Sum(_) | Kind::Void) | Err(Form::Product | Form::Signature) => Err(Form::Sum),
        Err(form) => Err(form),
    };
    let outside = |node: &'static str| Err(Form::Outside(node));
    match *types.value_type(word).ok_or(Form::Dangling)? {
        ValueType::Base(BaseType::Fixed(width)) => Ok(Kind::Word(width)),
        ValueType::Product(ref components) => {
            if !components.is_empty() {
                return Err(Form::Product);
            }
            Ok(Kind::Unit)
        },
        ValueType::Sum(ref summands) => match **summands {
            [] => Ok(Kind::Void),
            [first, second] => Ok(Kind::Sum(SumLayout([field(first)?, field(second)?]))),
            [..] => Err(Form::Sum),
        },
        ValueType::Thunk(_)
        | ValueType::Data { .. }
        | ValueType::Universe { .. }
        | ValueType::Element { .. } => Err(Form::Signature),
        ValueType::Base(BaseType::Integer) => outside("BaseType::Integer"),
        ValueType::Base(BaseType::String) => outside("BaseType::String"),
        ValueType::Base(BaseType::Numeric) => outside("BaseType::Numeric"),
        ValueType::Base(BaseType::Character) => outside("BaseType::Character"),
        ValueType::Base(BaseType::Float64) => outside("BaseType::Float64"),
        ValueType::Record(_) => outside("ValueType::Record"),
        ValueType::Patched { .. } => outside("ValueType::Patched"),
        ValueType::PathUniverse(..) => outside("ValueType::PathUniverse"),
        ValueType::Path { .. } => outside("ValueType::Path"),
        ValueType::Flow { .. } => outside("ValueType::Flow"),
        ValueType::Bridge { .. } => outside("ValueType::Bridge"),
        ValueType::Run { .. } => outside("ValueType::Run"),
        ValueType::Prefix { .. } => outside("ValueType::Prefix"),
        ValueType::Dialogue { .. } => outside("ValueType::Dialogue"),
        ValueType::Web => outside("ValueType::Web"),
        ValueType::Sigma { .. } => outside("ValueType::Sigma"),
        ValueType::List(_) => outside("ValueType::List"),
        ValueType::Lift { .. } => outside("ValueType::Lift"),
        ValueType::Row => outside("ValueType::Row"),
        ValueType::RowTail { .. } => outside("ValueType::RowTail"),
        ValueType::Abstract { .. } => outside("ValueType::Abstract"),
        ValueType::Staged { .. } => outside("ValueType::Staged"),
        ValueType::StaticPi { .. } => outside("ValueType::StaticPi"),
        ValueType::Unknown => outside("ValueType::Unknown"),
        ValueType::Stack { .. } => outside("ValueType::Stack"),
        ValueType::Session { .. } => outside("ValueType::Session"),
        ValueType::Capability { .. } => outside("ValueType::Capability"),
        ValueType::Buffer => outside("ValueType::Buffer"),
        ValueType::Qubit => outside("ValueType::Qubit"),
        ValueType::Kept { .. } => outside("ValueType::Kept"),
        ValueType::World { .. } => outside("ValueType::World"),
    }
}

/// The parameters and the result of a definition of type `signature`.
///
/// # Specification
/// - ensures: one kind for each arrow of the chain, the first one first, and
///   the kind of the returner at its end.
/// - fails: [`Form::Dangling`] for a type the arena does not hold, and
///   [`Form::Signature`] for a type that is not a thunk of arrows over words or
///   `Unit` to a returner of a word, `Unit` or `Void`.
/// - panics: none.
/// - intension: one read of the arena for each type of the chain, with no
///   recursion.
///
/// # Errors
///
/// As the failure clause states.
///
/// # Cost
/// - allocation: the kinds of the parameters, durable by the function
///
/// # Adequacy
/// - hypothesis: L3 — the types of the fixture give one parameter or none, and
///   a type with a thunk domain is refused.
/// - witness: `lower::tests::each_definition_of_the_fixture_becomes_an_object`
/// - witness: `lower::tests::a_thunk_parameter_is_refused`
#[spec(ensures: |ref ret| ret.is_err() || types.value_type(signature).is_some_and(|ty| matches!(*ty, ValueType::Thunk(_))))]
fn signature(
    types: &CoreArena,
    signature: ValueTypeId,
) -> Result<Signature, Form>
{
    let ValueType::Thunk(mut computation) = *types.value_type(signature).ok_or(Form::Dangling)?
    else {
        return Err(Form::Signature);
    };
    let mut parameters = Vec::new();
    loop {
        match *types.comp_type(computation).ok_or(Form::Dangling)? {
            CompType::Arrow { domain, codomain } => {
                let parameter = kind(types, domain)?;
                if parameter == Kind::Void {
                    return Err(Form::Signature);
                }
                parameters.push(parameter);
                computation = codomain;
            },
            // The row bounds what the body can do. The body lowers when each
            // of its nodes has a form, so the lowering does not read the row.
            CompType::Returner { result, .. } => {
                return Ok(Signature {
                    parameters: parameters.into_boxed_slice(),
                    result: kind(types, result)?,
                });
            },
            CompType::Returns { .. } => return Err(Form::Outside("CompType::Returns")),
            CompType::LinearArrow { .. } => return Err(Form::Outside("CompType::LinearArrow")),
            CompType::Pi { .. } => return Err(Form::Outside("CompType::Pi")),
            CompType::Element { .. } => return Err(Form::Outside("CompType::Element")),
            CompType::Unknown => return Err(Form::Outside("CompType::Unknown")),
            CompType::With { .. } => return Err(Form::Outside("CompType::With")),
            CompType::Codata { .. } => return Err(Form::Outside("CompType::Codata")),
        }
    }
}

/// The operation of the dialect for a native row, or the `checked_`
/// operation of the row.
///
/// # Specification
/// - ensures: the operation of [`Primitive::machine_operation`], such as
///   `wrapping_add` for `u8.wrapping_add` and `not` for `u64.not`, or the
///   operation of [`Primitive::checked_operation`], such as `checked_sub` for
///   `u64.checked_sub`. The lowering reads no text of the name of a row.
/// - fails: [`Form::Native`] for a row with neither.
/// - panics: none.
///
/// # Errors
///
/// As the failure clause states.
///
/// # Adequacy
/// - hypothesis: L3 — `u8.wrapping_add` gives `gandr.wrapping_add` in the text
///   of the fixture, which compiles. Each row of the native table, at each
///   width, lowers to an operation and compiles to its symbol. A row with no
///   operation fails that test by its name. Each bit row of each width gives
///   its operation in the text. On each pair of edge operands, the compiled
///   answer of each row is the answer of the evaluator.
/// - witness: `lower::tests::wrapped_gives_the_pattern_of_the_greatest_byte`
/// - witness: `lower::tests::each_row_of_the_native_table_becomes_an_object`
/// - witness: `lower::tests::each_bit_row_of_each_width_becomes_its_operation`
/// - witness: `lower::tests::the_compiled_answer_of_each_row_is_the_answer_of_the_evaluator`
#[spec(ensures: |ret| ret.is_ok() == (primitive.machine_operation().is_some() || primitive.checked_operation().is_some()))]
fn native(primitive: Primitive) -> Result<Native, Form>
{
    if let Some(machine) = primitive.machine_operation() {
        return Ok(Native::Word(match machine.instruction {
            MachineInstruction::Add => Operation::WrappingAdd,
            MachineInstruction::Sub => Operation::WrappingSub,
            MachineInstruction::Mul => Operation::WrappingMul,
            MachineInstruction::And => Operation::And,
            MachineInstruction::Or => Operation::Or,
            MachineInstruction::Xor => Operation::Xor,
            MachineInstruction::Not => Operation::Not,
        }));
    }
    let checked = primitive.checked_operation().ok_or(Form::Native)?;
    Ok(Native::Checked(match checked.instruction {
        CheckedInstruction::Add => Checked::Add,
        CheckedInstruction::Sub => Checked::Sub,
        CheckedInstruction::Mul => Checked::Mul,
        CheckedInstruction::Shl => Checked::Shl,
        CheckedInstruction::Shr => Checked::Shr,
    }))
}

/// The name of the variant of `literal`, as [`Form::Outside`] holds it.
///
/// # Specification
/// - ensures: `Literal::` and the name of the variant.
/// - panics: none.
/// - executable: none — the answer is one text for each variant.
///
/// # Adequacy
/// - hypothesis: L3 — a literal of `Integer` is refused by its name.
/// - witness: `lower::tests::a_node_outside_the_lowering_is_refused_by_its_name`
const fn literal_name(literal: &Literal) -> &'static str
{
    match *literal {
        Literal::Integer(_) => "Literal::Integer",
        Literal::Text(_) => "Literal::Text",
        Literal::Numeric(_) => "Literal::Numeric",
        Literal::Character(_) => "Literal::Character",
        Literal::Float64(_) => "Literal::Float64",
        Literal::Fixed(_) => "Literal::Fixed",
    }
}

/// The name of the variant of `tag`, as [`Form::Outside`] holds it.
///
/// # Specification
/// - ensures: `ConstructorTag::` and the name of the variant.
/// - panics: none.
/// - executable: none — the answer is one text for each variant.
///
/// # Adequacy
/// - hypothesis: L3 — the empty list is refused by its name.
/// - witness: `lower::tests::a_node_outside_the_lowering_is_refused_by_its_name`
const fn constructor_name(tag: &ConstructorTag) -> &'static str
{
    match *tag {
        ConstructorTag::Tuple(_) => "ConstructorTag::Tuple",
        ConstructorTag::Record(_) => "ConstructorTag::Record",
        ConstructorTag::ListNil => "ConstructorTag::ListNil",
        ConstructorTag::ListCons => "ConstructorTag::ListCons",
        ConstructorTag::Injection(_) => "ConstructorTag::Injection",
        ConstructorTag::Lift(_) => "ConstructorTag::Lift",
        ConstructorTag::Data { .. } => "ConstructorTag::Data",
        ConstructorTag::Recorded(_) => "ConstructorTag::Recorded",
        ConstructorTag::Dialogue(_) => "ConstructorTag::Dialogue",
        ConstructorTag::Web(_) => "ConstructorTag::Web",
    }
}

/// The name of the variant of `command`, as [`Form::Outside`] holds it.
///
/// # Specification
/// - ensures: `CommandNode::` and the name of the variant.
/// - panics: none.
/// - executable: none — the answer is one text for each variant.
///
/// # Adequacy
/// - hypothesis: L3 — a `perform` in a body is refused by its name.
/// - witness: `lower::tests::a_node_outside_the_lowering_is_refused_by_its_name`
const fn command_name(command: &CommandNode) -> &'static str
{
    match *command {
        CommandNode::Perform { .. } => "CommandNode::Perform",
        CommandNode::Handle { .. } => "CommandNode::Handle",
        CommandNode::Resume { .. } => "CommandNode::Resume",
        CommandNode::Abandon { .. } => "CommandNode::Abandon",
        CommandNode::Reset { .. } => "CommandNode::Reset",
        CommandNode::Shift { .. } => "CommandNode::Shift",
        CommandNode::Cut { .. } => "CommandNode::Cut",
        CommandNode::Deliver { .. } => "CommandNode::Deliver",
        CommandNode::Memory { .. } => "CommandNode::Memory",
        CommandNode::World { .. } => "CommandNode::World",
        CommandNode::Session { .. } => "CommandNode::Session",
    }
}

/// The name of the variant of `producer`, as [`Form::Outside`] holds it.
///
/// # Specification
/// - ensures: `ProducerNode::` and the name of the variant.
/// - panics: none.
/// - executable: none — the answer is one text for each variant.
///
/// # Adequacy
/// - hypothesis: L3 — a reified stack in a body is refused by its name.
/// - witness: `lower::tests::a_node_outside_the_lowering_is_refused_by_its_name`
const fn producer_name(producer: &ProducerNode) -> &'static str
{
    match *producer {
        ProducerNode::Reify(_) => "ProducerNode::Reify",
        ProducerNode::Primitive { .. } => "ProducerNode::Primitive",
        ProducerNode::Decompose(_) => "ProducerNode::Decompose",
        ProducerNode::Variable { .. } => "ProducerNode::Variable",
        ProducerNode::Constant(_) => "ProducerNode::Constant",
        ProducerNode::Literal(_) => "ProducerNode::Literal",
        ProducerNode::Code(_) => "ProducerNode::Code",
        ProducerNode::Constructor { .. } => "ProducerNode::Constructor",
        ProducerNode::Thunk { .. } => "ProducerNode::Thunk",
        ProducerNode::Fixpoint { .. } => "ProducerNode::Fixpoint",
        ProducerNode::Cocase { .. } => "ProducerNode::Cocase",
        ProducerNode::Closure { .. } => "ProducerNode::Closure",
        ProducerNode::Mu { .. } => "ProducerNode::Mu",
    }
}

/// The name of the variant of `consumer`, as [`Form::Outside`] holds it.
///
/// # Specification
/// - ensures: `ConsumerNode::` and the name of the variant.
/// - panics: none.
/// - executable: none — the answer is one text for each variant.
///
/// # Adequacy
/// - hypothesis: L3 — a select in a body is refused by its name.
/// - witness: `lower::tests::a_node_outside_the_lowering_is_refused_by_its_name`
const fn consumer_name(consumer: &ConsumerNode) -> &'static str
{
    match *consumer {
        ConsumerNode::Covariable(_) => "ConsumerNode::Covariable",
        ConsumerNode::MuTilde { .. } => "ConsumerNode::MuTilde",
        ConsumerNode::MuTildeAll { .. } => "ConsumerNode::MuTildeAll",
        ConsumerNode::Destructor { .. } => "ConsumerNode::Destructor",
        ConsumerNode::Case { .. } => "ConsumerNode::Case",
        ConsumerNode::DataCase { .. } => "ConsumerNode::DataCase",
        ConsumerNode::Select { .. } => "ConsumerNode::Select",
        ConsumerNode::ListFold { .. } => "ConsumerNode::ListFold",
        ConsumerNode::Top => "ConsumerNode::Top",
    }
}

/// What a call of one definition needs: its signature, and the name of its
/// function.
#[derive(Clone, Debug)]
struct Callee<'name>
{
    /// The parameters and the result.
    signature: Signature,
    /// The function that a call or a jump enters.
    name: Symbol<'name>,
}

/// What a covariable of a body names: the return continuation, or the
/// consumer that a naming cut gives its capture.
#[derive(Clone, Copy, Debug)]
enum Continuation
{
    /// The return continuation of the function.
    Return,
    /// The consumer of a naming cut `⟨μα. s | k⟩`, with the scope of the cut.
    Named
    {
        /// The consumer `k`.
        consumer: ConsumerId,
        /// The count of the bound producer variables at the cut.
        scope: usize,
        /// The count of the continuations at the cut, which is the place of
        /// this continuation.
        continuations: usize,
        /// The floor at the cut.
        floor: usize,
        /// The count of the waiting blocks at the cut.
        pending: usize,
        /// The block that receives a delivery from a branch of a case after
        /// the cut, once a branch makes it.
        join: Option<Join>,
    },
}

/// A block of the function that receives the delivery of each branch of a
/// case to one continuation outside the case.
#[derive(Clone, Copy, Debug)]
struct Join
{
    /// The block.
    block: Block,
    /// The argument of the block, or `None` for the unit.
    argument: Option<Value>,
}

/// Where the result of a call goes.
#[derive(Clone, Copy, Debug)]
enum After
{
    /// The return continuation, so the call is a jump.
    Tail,
    /// A consumer that receives the result: a binder, a covariable of a
    /// naming cut, or a case.
    Deliver(ConsumerId),
}

/// A branch of a case over a sum in a word, which waits for its block.
#[derive(Clone, Copy, Debug)]
struct Branch
{
    /// The block of the branch.
    block: Block,
    /// The body of the arm.
    body: CommandId,
    /// The sum.
    sum: Value,
    /// The field of the summand of the arm.
    field: Field,
    /// The count of the bound producer variables at the case.
    scope: usize,
    /// The count of the continuations at the case.
    continuations: usize,
}

/// A block that waits for its operations.
#[derive(Clone, Copy, Debug)]
enum Waiting
{
    /// A branch of a case.
    Arm(Branch),
    /// The join of a continuation of a naming cut, which runs the consumer of
    /// the cut on the argument of the block.
    Join
    {
        /// The block and its argument.
        join: Join,
        /// The operand of the argument, as the consumer receives it.
        bound: Operand,
        /// The consumer of the cut.
        consumer: ConsumerId,
        /// The count of the bound producer variables at the cut.
        scope: usize,
        /// The place of the continuation of the cut.
        continuations: usize,
        /// The floor at the cut.
        floor: usize,
    },
}

/// The state of the lowering of one function.
struct Lowering<'arena, 'name>
{
    /// The command arena of the definitions.
    arena: &'arena CommandArena,
    /// The callee of each constant, by admission position.
    callees: &'arena [Callee<'name>],
    /// The function so far.
    function: Function<'name>,
    /// The operand of each bound producer variable, the innermost last.
    scope: Vec<Operand>,
    /// Whether the self binder of a recursive thunk is just outside `scope`.
    recursion: Recursion,
    /// What each covariable names, the innermost last. The first one is the
    /// return continuation.
    continuations: Vec<Continuation>,
    /// The blocks that wait for their operations, the next one last.
    pending: Vec<Waiting>,
    /// The count of the continuations at the innermost case over a sum in a
    /// word whose branch is lowered now. A delivery from the branch to a
    /// continuation below it, except the return continuation, goes to the
    /// join of that continuation.
    floor: usize,
}

impl Lowering<'_, '_>
{
    /// A new value of type `ty`.
    ///
    /// # Specification
    /// - ensures: the value after each value so far, of type `ty`.
    /// - panics: none.
    ///
    /// # Cost
    /// - allocation: one type, growth within the function
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each value of the fixture has its own name, and the
    ///   text compiles.
    /// - witness: `lower::tests::each_definition_of_the_fixture_becomes_an_object`
    #[spec(
        captures: [before = self.function.types.len()],
        ensures: |ret| ret.0 == before && self.function.types.len() == before.saturating_add(1),
    )]
    fn fresh(
        &mut self,
        ty: Typed,
    ) -> Value
    {
        let value = Value(self.function.types.len());
        self.function.types.push(ty);
        value
    }

    /// The constant of the function when the producer variable `index` names
    /// the self binder of its recursive thunk.
    ///
    /// # Specification
    /// - ensures: `Some` of the constant of the function exactly when the
    ///   function is recursive and `index` counts past each bound producer
    ///   variable to the binder just outside them.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a call of the self binder in a tail is a jump to the
    ///   function, another call is a call of it, and the self binder as a value
    ///   is refused. Inside a branch of a case, the self binder is still the
    ///   binder just outside the scope, and the countdown runs to its end.
    /// - witness: `lower::tests::a_fixpoint_at_the_head_of_a_definition_is_its_function`
    /// - witness: `lower::tests::a_fixpoint_inside_a_body_is_refused_by_name`
    /// - witness: `lower::tests::a_countdown_from_a_hundred_million_jumps_and_exits_with_zero`
    #[spec(ensures: |ret| ret.is_some() == (self.recursion == Recursion::Recursive
        && usize::try_from(u32::from(index)).is_ok_and(|place| place == self.scope.len())))]
    fn itself(
        &self,
        index: DeBruijnIndex,
    ) -> Option<ConstantIndex>
    {
        let place = usize::try_from(u32::from(index)).ok()?;
        (self.recursion == Recursion::Recursive && place == self.scope.len())
            .then_some(self.function.constant)
    }

    /// The operand of a producer that an operation reads: a variable, a
    /// literal, the unit or an injection.
    ///
    /// # Specification
    /// - ensures: the operand of the variable, a new constant of the literal,
    ///   [`Operand::Unit`] for the unit, the tuple of no fields, which needs no
    ///   step, or [`Operand::Injected`] for an injection of a word or of the
    ///   unit, which needs the step of its field or none.
    /// - fails: [`Form::Dangling`] for a producer the arena does not hold;
    ///   [`Form::Product`] for a tuple with a field; [`Form::Unbound`] for a
    ///   variable outside the scope or in the linear zone; [`Form::Delivery`]
    ///   for a constant or an operation; [`Form::Closure`] for a thunk, a
    ///   copattern object, a capture or the self binder of a recursive thunk;
    ///   [`Form::Sum`] for an injection of a sum; [`Form::Destructor`] for an
    ///   injection with other children than one field; [`Form::Fixpoint`] for a
    ///   recursive thunk.
    /// - panics: none.
    ///
    /// # Errors
    ///
    /// As the failure clause states.
    ///
    /// # Cost
    /// - allocation: one step and one width for a literal, growth within the
    ///   function
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the parameter and the literals of the fixture are
    ///   read, the unit is read with no step, a variable past the scope is
    ///   refused, a thunk, a recursive thunk, the self binder and a tuple of
    ///   one field are refused, and the injections of the case fixtures are
    ///   read.
    /// - witness: `lower::tests::each_definition_of_the_fixture_becomes_an_object`
    /// - witness: `lower::tests::a_definition_of_unit_returns_no_value`
    /// - witness: `lower::tests::a_variable_past_the_scope_is_unbound`
    /// - witness: `lower::tests::a_thunk_inside_a_body_is_a_closure`
    /// - witness: `lower::tests::a_fixpoint_inside_a_body_is_refused_by_name`
    /// - witness: `lower::tests::a_tuple_or_a_product_with_a_component_is_refused_by_name`
    /// - witness: `lower::tests::each_branch_of_each_case_runs_and_exits_with_its_answer`
    /// - witness: `lower::tests::a_sum_with_no_layout_is_refused_by_name`
    #[spec(
        captures: [before = self.function.steps.len()],
        ensures: |ref ret| ret.is_err() || self.function.steps.len() <= before.saturating_add(1),
    )]
    fn operand(
        &mut self,
        producer: ProducerId,
    ) -> Result<Operand, Form>
    {
        // An injection reads its field as a plain operand, in the same match.
        let mut node = self.arena.producer(producer).ok_or(Form::Dangling)?;
        let mut injection = None;
        if let &ProducerNode::Constructor {
            tag: ConstructorTag::Injection(summand),
            ref producers,
            ref consumers,
            ..
        } = node
        {
            let (&[inner], &[]) = (&**producers, &**consumers)
            else {
                return Err(Form::Destructor);
            };
            node = self.arena.producer(inner).ok_or(Form::Dangling)?;
            injection = Some(summand);
        }
        let plain = match *node {
            ProducerNode::Variable {
                zone: Zone::Intuitionistic,
                index,
            } => {
                if self.itself(index).is_some() {
                    return Err(Form::Closure);
                }
                let index = usize::try_from(u32::from(index)).map_err(|_overflow| Form::Unbound)?;
                self.scope
                    .iter()
                    .rev()
                    .nth(index)
                    .copied()
                    .ok_or(Form::Unbound)
            },
            ProducerNode::Variable {
                zone: Zone::Linear, ..
            } => Err(Form::Unbound),
            ProducerNode::Literal(Literal::Fixed(literal)) => {
                let value = self.fresh(Typed::Word(literal.width()));
                self.function.steps.push(Step::Constant { value, literal });
                Ok(Operand::Word(value))
            },
            ProducerNode::Literal(ref literal) => Err(Form::Outside(literal_name(literal))),
            ProducerNode::Constructor {
                tag: ConstructorTag::Tuple(_),
                ref producers,
                ref consumers,
                ..
            } => {
                if !producers.is_empty() || !consumers.is_empty() {
                    return Err(Form::Product);
                }
                Ok(Operand::Unit)
            },
            ProducerNode::Constructor {
                tag: ConstructorTag::Injection(_) | ConstructorTag::Data { .. },
                ..
            } => Err(Form::Sum),
            ProducerNode::Constructor { ref tag, .. } => Err(Form::Outside(constructor_name(tag))),
            ProducerNode::Constant(_) | ProducerNode::Primitive { .. } => Err(Form::Delivery),
            ProducerNode::Fixpoint { .. } => Err(Form::Fixpoint),
            ProducerNode::Thunk { .. } | ProducerNode::Cocase { .. } | ProducerNode::Mu { .. } => {
                Err(Form::Closure)
            },
            ProducerNode::Reify(_) => Err(Form::Outside("ProducerNode::Reify")),
            ProducerNode::Decompose(_) => Err(Form::Outside("ProducerNode::Decompose")),
            ProducerNode::Code(_) => Err(Form::Outside("ProducerNode::Code")),
            ProducerNode::Closure { .. } => Err(Form::Outside("ProducerNode::Closure")),
        }?;
        let Some(summand) = injection
        else {
            return Ok(plain);
        };
        let field = match plain {
            Operand::Word(value) => Payload::Word(value),
            Operand::Unit => Payload::Unit,
            Operand::Sum(_) | Operand::Injected { .. } => return Err(Form::Sum),
        };
        Ok(Operand::Injected { summand, field })
    }

    /// The word of a producer that a native operation reads.
    ///
    /// # Specification
    /// - ensures: the word of [`Self::operand`], after one step or none.
    /// - fails: as [`Self::operand`], and [`Form::Delivery`] for the unit,
    ///   which has no word.
    /// - panics: none.
    ///
    /// # Errors
    ///
    /// As the failure clause states.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the operands of `inc` and of `wrapped` are words, and
    ///   the unit as an operand of a native operation is refused.
    /// - witness: `lower::tests::wrapped_gives_the_pattern_of_the_greatest_byte`
    /// - witness: `lower::tests::a_definition_of_unit_returns_no_value`
    #[spec(
        captures: [before = self.function.steps.len()],
        ensures: |ref ret| ret.is_err() || self.function.steps.len() <= before.saturating_add(1),
    )]
    fn word(
        &mut self,
        producer: ProducerId,
    ) -> Result<Value, Form>
    {
        match self.operand(producer)? {
            Operand::Word(value) => Ok(value),
            Operand::Unit | Operand::Sum(_) | Operand::Injected { .. } => Err(Form::Delivery),
        }
    }

    /// The operand of a producer that a cut delivers: an operand, a native
    /// operation over its words, or the sum of a `checked_` row.
    ///
    /// # Specification
    /// - ensures: the value of an operand, or what [`Self::row`] gives for a
    ///   native row with its arguments.
    /// - fails: as [`Self::operand`] and [`Self::row`].
    /// - panics: none.
    ///
    /// # Errors
    ///
    /// As the failure clause states.
    ///
    /// # Cost
    /// - allocation: the steps and the types of the operation, growth within
    ///   the function
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the operation of `inc` and of `wrapped` is lowered,
    ///   each bit row of each width is lowered, each branch of a `checked_` row
    ///   runs, and the text compiles.
    /// - witness: `lower::tests::wrapped_gives_the_pattern_of_the_greatest_byte`
    /// - witness: `lower::tests::each_bit_row_of_each_width_becomes_its_operation`
    /// - witness: `lower::tests::each_branch_of_a_checked_row_runs`
    #[spec(
        captures: [before = self.function.steps.len()],
        ensures: |ref ret| ret.is_err() || self.function.steps.len() <= before.saturating_add(3),
    )]
    fn value(
        &mut self,
        producer: ProducerId,
    ) -> Result<Operand, Form>
    {
        let &ProducerNode::Primitive {
            primitive,
            arguments,
        } = self.arena.producer(producer).ok_or(Form::Dangling)?
        else {
            return self.operand(producer);
        };
        self.row(primitive, arguments)
    }

    /// The native operation of `primitive` over the words of `arguments`.
    ///
    /// # Specification
    /// - ensures: the result of a new native operation of the width of its row,
    ///   or a sum of that width and `Unit` for a `checked_` row.
    /// - fails: as [`Self::word`] for an argument, and [`Form::Native`] for a
    ///   row with no operation of the dialect, for a result of another kind
    ///   than its row, or for a count of arguments other than its arity.
    /// - panics: none.
    ///
    /// # Errors
    ///
    /// As the failure clause states.
    ///
    /// # Cost
    /// - allocation: the steps and the types of the operation, growth within
    ///   the function
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the operation of `inc`, of `wrapped` and of a forced
    ///   native row is lowered, each bit row of each width is lowered, each
    ///   branch of a `checked_` row runs, and the text compiles.
    /// - witness: `lower::tests::wrapped_gives_the_pattern_of_the_greatest_byte`
    /// - witness: `lower::tests::each_bit_row_of_each_width_becomes_its_operation`
    /// - witness: `lower::tests::each_branch_of_a_checked_row_runs`
    /// - witness: `lower::tests::a_forced_native_row_in_a_body_is_its_operation`
    #[spec(
        captures: [before = self.function.steps.len()],
        ensures: |ref ret| ret.is_err() || self.function.steps.len() <= before.saturating_add(3),
    )]
    fn row(
        &mut self,
        primitive: Primitive,
        arguments: Arguments<ProducerId>,
    ) -> Result<Operand, Form>
    {
        let native = native(primitive)?;
        if arguments.len() != primitive.arguments().len() {
            return Err(Form::Native);
        }
        let operands = match arguments {
            Arguments::Unary(only) => Arguments::Unary(self.word(only)?),
            Arguments::Binary([left, right]) => {
                Arguments::Binary([self.word(left)?, self.word(right)?])
            },
        };
        match (native, primitive.result(), operands) {
            (Native::Word(operation), PrimitiveType::Fixed(width), _) => {
                let value = self.fresh(Typed::Word(width));
                self.function.steps.push(Step::Native {
                    value,
                    operation,
                    operands,
                });
                Ok(Operand::Word(value))
            },
            (
                Native::Checked(operation),
                PrimitiveType::Checked(width),
                Arguments::Binary(operands),
            ) => {
                let value = self.fresh(Typed::Sum(SumLayout([Field::Word(width), Field::Unit])));
                self.function.steps.push(Step::Checked {
                    value,
                    operation,
                    width,
                    operands,
                });
                Ok(Operand::Sum(value))
            },
            (Native::Word(_), PrimitiveType::Checked(_), _)
            | (Native::Checked(_), PrimitiveType::Fixed(_), _)
            | (Native::Checked(_), PrimitiveType::Checked(_), Arguments::Unary(_))
            | (
                _,
                PrimitiveType::Integer
                | PrimitiveType::Boolean
                | PrimitiveType::Text
                | PrimitiveType::Float64,
                _,
            ) => Err(Form::Native),
        }
    }

    /// The native row that the thunk `producer` stands for, when it is the
    /// row's own function: `thunk(cocase{apply(x₁; β₁) ⇒ … cocase{apply(xₙ;
    /// βₙ) ⇒ ⟨row(x₁, …, xₙ) |+ βₙ⟩}})`, each object cut against the
    /// covariable that its binder opens.
    ///
    /// # Specification
    /// - ensures: the row when the thunk opens one `apply` arm for each
    ///   argument of the row, each object or the row is cut against the
    ///   innermost covariable, and the arguments of the row are the parameters
    ///   of the arms in order; `None` for each other producer.
    /// - panics: none.
    /// - intension: one turn of the loop for each arm, with no recursion and no
    ///   allocation.
    /// - executable: none — the shape is the statement, and the witness lowers
    ///   the shape that the elaboration gives to a native row in a body.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a forced native row of one and of two arguments is
    ///   its row; a thunk of a row whose arguments are swapped is a closure.
    /// - witness: `lower::tests::a_forced_native_row_in_a_body_is_its_operation`
    fn forced_row(
        &self,
        producer: ProducerId,
    ) -> Option<Primitive>
    {
        let &ProducerNode::Thunk { body } = self.arena.producer(producer)?
        else {
            return None;
        };
        let innermost = |consumer: ConsumerId| {
            matches!(
                self.arena.consumer(consumer),
                Some(&ConsumerNode::Covariable(index)) if u32::from(index) == 0
            )
        };
        let mut command = body;
        let mut arity = 0_u32;
        loop {
            let &CommandNode::Cut {
                producer, consumer, ..
            } = self.arena.command(command)?
            else {
                return None;
            };
            if !innermost(consumer) {
                return None;
            }
            match *self.arena.producer(producer)? {
                ProducerNode::Cocase { ref arms } => {
                    let &[
                        CopatternArm {
                            destructor: DestructorTag::Apply,
                            body,
                        },
                    ] = &**arms
                    else {
                        return None;
                    };
                    arity = arity.checked_add(1)?;
                    command = body;
                },
                ProducerNode::Primitive {
                    primitive,
                    arguments,
                } => {
                    let parameters = match arguments {
                        Arguments::Unary(only) => [Some(only), None],
                        Arguments::Binary([left, right]) => [Some(left), Some(right)],
                    };
                    let named = parameters.iter().flatten().enumerate().all(|(place, &argument)| {
                        let place = u32::try_from(place).unwrap_or(u32::MAX);
                        matches!(
                            self.arena.producer(argument),
                            Some(&ProducerNode::Variable { zone: Zone::Intuitionistic, index })
                                if arity.checked_sub(1).and_then(|last| last.checked_sub(place)) == Some(u32::from(index))
                        )
                    });
                    let count = u32::try_from(arguments.len()).ok()?;
                    return (named && count == arity).then_some(primitive);
                },
                ProducerNode::Reify(_)
                | ProducerNode::Decompose(_)
                | ProducerNode::Variable { .. }
                | ProducerNode::Constant(_)
                | ProducerNode::Literal(_)
                | ProducerNode::Code(_)
                | ProducerNode::Constructor { .. }
                | ProducerNode::Thunk { .. }
                | ProducerNode::Fixpoint { .. }
                | ProducerNode::Closure { .. }
                | ProducerNode::Mu { .. } => return None,
            }
        }
    }

    /// Lower the native row `primitive` against the frame `force(f)` of its
    /// own function, and give the command after it.
    ///
    /// # Specification
    /// - ensures: the operation of [`Self::row`] over the argument of each
    ///   `apply` frame of `f`, one frame for each argument of the row, then its
    ///   result goes to the consumer after the frames.
    /// - fails: [`Form::Delivery`] for fewer `apply` frames than the arguments
    ///   of the row, or a frame of `force` among them; [`Form::Destructor`] for
    ///   an `apply` frame with other children; and as [`Self::row`] and
    ///   [`Self::deliver`].
    /// - panics: none.
    ///
    /// # Errors
    ///
    /// As the failure clause states.
    ///
    /// # Cost
    /// - allocation: the steps and the types of the operation, growth within
    ///   the function
    ///
    /// # Adequacy
    /// - hypothesis: L3 — `u8.wrapping_add 255u8 3u8` in a body gives
    ///   `gandr.wrapping_add` and runs to 2, and a checked row in a body gives
    ///   its sum to a case.
    /// - witness: `lower::tests::a_forced_native_row_in_a_body_is_its_operation`
    fn forced(
        &mut self,
        primitive: Primitive,
        frame: ConsumerId,
    ) -> Result<Option<CommandId>, Form>
    {
        let mut taken: [Option<ProducerId>; 2] = [None, None];
        let mut frame = frame;
        for slot in taken.iter_mut().take(primitive.arguments().len()) {
            let &ConsumerNode::Destructor {
                tag,
                ref producers,
                ref consumers,
            } = self.arena.consumer(frame).ok_or(Form::Dangling)?
            else {
                return Err(Form::Delivery);
            };
            if tag != DestructorTag::Apply {
                return Err(Form::Delivery);
            }
            let (&[argument], &[next]) = (&**producers, &**consumers)
            else {
                return Err(Form::Destructor);
            };
            *slot = Some(argument);
            frame = next;
        }
        let arguments = match taken {
            [Some(only), None] => Arguments::Unary(only),
            [Some(left), Some(right)] => Arguments::Binary([left, right]),
            [None, _] => return Err(Form::Native),
        };
        let operand = self.row(primitive, arguments)?;
        self.deliver(operand, frame)
    }

    /// Lower the call of the constant `callee` against the frame `force(f)`,
    /// and give the command after it, or `None` after a jump or a return.
    ///
    /// # Specification
    /// - ensures: one operand for each `apply` frame of `f` whose argument has
    ///   a word or a sum, then a call whose result goes to the consumer after
    ///   the frames, or a jump when that consumer names the return
    ///   continuation. A call of a callee of `Unit` has no result, and its
    ///   consumer receives the unit. A call of a callee of `Void` that is not a
    ///   jump ends its block with `llvm.unreachable`, and its consumer gets no
    ///   step. An injection as an argument of a sum gets its words before the
    ///   call.
    /// - fails: [`Form::Unbound`] for a constant with no definition or a
    ///   covariable that names nothing; [`Form::Delivery`] for a count of
    ///   arguments other than the parameters of the callee, an argument of
    ///   another kind than its parameter, or a frame of `force` after the
    ///   frames; [`Form::Destructor`] for an `apply` frame with other children;
    ///   and as [`Self::operand`] for an argument and [`Self::deliver`] for the
    ///   result.
    /// - panics: none.
    ///
    /// # Errors
    ///
    /// As the failure clause states.
    ///
    /// # Cost
    /// - allocation: the operands and the step of the call, growth within the
    ///   function
    ///
    /// # Adequacy
    /// - hypothesis: L3 — `twice` calls `inc` and jumps to `inc`, `answer` and
    ///   `main` call with no argument, a call of a callee of `Unit` binds no
    ///   word, a call with two arguments to `inc` is refused, and an injection
    ///   goes to a parameter of a sum.
    /// - witness: `lower::tests::twice_calls_inc_and_jumps_to_inc`
    /// - witness: `lower::tests::a_definition_of_unit_returns_no_value`
    /// - witness: `lower::tests::a_call_with_more_arguments_than_parameters_is_refused`
    /// - witness: `lower::tests::a_let_of_a_call_with_a_call_as_its_argument_runs`
    /// - witness: `lower::tests::each_branch_of_each_case_runs_and_exits_with_its_answer`
    #[spec(
        captures: [before = self.function.steps.len()],
        ensures: |ref ret| ret.is_err() || self.function.steps.len() > before,
    )]
    fn call(
        &mut self,
        callee: ConstantIndex,
        frame: ConsumerId,
    ) -> Result<Option<CommandId>, Form>
    {
        let callees = self.callees;
        let Callee {
            ref signature,
            name: callee,
        } = *callees.get(usize::from(callee)).ok_or(Form::Unbound)?;
        let mut arguments = Vec::new();
        let mut frame = frame;
        let after = loop {
            match *self.arena.consumer(frame).ok_or(Form::Dangling)? {
                ConsumerNode::Destructor {
                    tag: DestructorTag::Apply,
                    ref producers,
                    ref consumers,
                } => {
                    let (&[argument], &[next]) = (&**producers, &**consumers)
                    else {
                        return Err(Form::Destructor);
                    };
                    arguments.push(argument);
                    frame = next;
                },
                ConsumerNode::Destructor {
                    tag: DestructorTag::Force,
                    ..
                } => return Err(Form::Delivery),
                ConsumerNode::Destructor {
                    tag: DestructorTag::Project(_),
                    ..
                } => return Err(Form::Outside("DestructorTag::Project")),
                ConsumerNode::Covariable(index) => match self.continuation(index)? {
                    Continuation::Return => break After::Tail,
                    Continuation::Named { .. } => break After::Deliver(frame),
                },
                ConsumerNode::MuTilde { .. } | ConsumerNode::Case { .. } => {
                    break After::Deliver(frame);
                },
                ConsumerNode::DataCase { .. } => return Err(Form::Sum),
                ConsumerNode::MuTildeAll { .. } => {
                    return Err(Form::Outside("ConsumerNode::MuTildeAll"));
                },
                ConsumerNode::Select { .. } => return Err(Form::Outside("ConsumerNode::Select")),
                ConsumerNode::ListFold { .. } => {
                    return Err(Form::Outside("ConsumerNode::ListFold"));
                },
                ConsumerNode::Top => return Err(Form::Outside("ConsumerNode::Top")),
            }
        };
        if arguments.len() != signature.parameters.len() {
            return Err(Form::Delivery);
        }
        let start = OperandIndex(self.function.operands.len());
        for (argument, &parameter) in arguments.into_iter().zip(&signature.parameters) {
            match (self.operand(argument)?, parameter) {
                (Operand::Word(value) | Operand::Sum(value), Kind::Word(_) | Kind::Sum(_)) => {
                    self.function.operands.push(value);
                },
                (Operand::Injected { summand, field }, Kind::Sum(layout)) => {
                    let value = self.inject(summand, field, layout)?;
                    self.function.operands.push(value);
                },
                (Operand::Unit, Kind::Unit) => {},
                (
                    Operand::Word(_) | Operand::Sum(_) | Operand::Injected { .. },
                    Kind::Unit | Kind::Void,
                )
                | (Operand::Unit, Kind::Word(_) | Kind::Sum(_) | Kind::Void)
                | (Operand::Injected { .. }, Kind::Word(_)) => {
                    return Err(Form::Delivery);
                },
            }
        }
        let end = OperandIndex(self.function.operands.len());
        let After::Deliver(consumer) = after
        else {
            self.function.steps.push(Step::Jump { callee, start, end });
            return Ok(None);
        };
        let (value, bound) = match signature.result {
            Kind::Word(width) => {
                let value = self.fresh(Typed::Word(width));
                (Some(value), Operand::Word(value))
            },
            Kind::Sum(layout) => {
                let value = self.fresh(Typed::Sum(layout));
                (Some(value), Operand::Sum(value))
            },
            Kind::Unit | Kind::Void => (None, Operand::Unit),
        };
        self.function.steps.push(Step::Call {
            value,
            callee,
            start,
            end,
        });
        if signature.result == Kind::Void {
            self.function.steps.push(Step::Unreachable);
            return Ok(None);
        }
        self.deliver(bound, consumer)
    }

    /// Lower the body `command` of the function to its last step.
    ///
    /// # Specification
    /// - ensures: one step for each operation of the table of the module, in
    ///   the order of the run. The last step is a return, a jump or an
    ///   `llvm.unreachable` after a call of `Void`. A naming cut `⟨μα. s | k⟩`
    ///   gives no step: `α` names `k`, and `s` follows. The function of a
    ///   native row against a frame of `force` is the operation of the row, as
    ///   [`Self::forced`] states. A case over a sum in a word ends its block
    ///   with a switch, and each of its branches follows in a block of its own,
    ///   the first branch first.
    /// - fails: [`Form::Dangling`] for a node the arena does not hold;
    ///   [`Form::Unbound`] for a covariable that names nothing;
    ///   [`Form::Destructor`] for a frame of `force` with other children;
    ///   [`Form::Closure`] for an `apply` frame against an object, for a frame
    ///   of `force` against a thunk that is not the function of a native row,
    ///   and for a negative cut of a capture against a binder `μ̃`;
    ///   [`Form::Delivery`] for an `apply` frame against another producer or a
    ///   frame of `force` against a producer that is not a constant, the self
    ///   binder of the function or a thunk; [`Form::Fixpoint`] for a recursive
    ///   thunk inside the body; and as [`Self::value`], [`Self::call`],
    ///   [`Self::forced`], [`Self::deliver`] and [`Self::resume`].
    /// - panics: none.
    /// - intension: one turn of the loop for each command of the body, with no
    ///   recursion. The stack of the continuations holds one name for each
    ///   naming cut, and no command. The stack of the branches holds one entry
    ///   for each branch that waits for its block.
    ///
    /// # Errors
    ///
    /// As the failure clause states.
    ///
    /// # Cost
    /// - allocation: the steps, the values and the operands, growth within the
    ///   function
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each definition of the fixture ends with its return
    ///   or its jump, a thunk in a body is refused, a `let` of a call or of a
    ///   native operation with a call as its operand runs, each branch of a
    ///   case runs, and the self binder of a recursive definition is its
    ///   function. A negative cut of a capture against a binder is refused, and
    ///   a positive one runs the capture. A native row in a body runs as its
    ///   operation.
    /// - witness: `lower::tests::each_definition_of_the_fixture_becomes_an_object`
    /// - witness: `lower::tests::a_thunk_inside_a_body_is_a_closure`
    /// - witness: `lower::tests::a_let_of_a_call_with_a_call_as_its_argument_runs`
    /// - witness: `lower::tests::each_branch_of_each_case_runs_and_exits_with_its_answer`
    /// - witness: `lower::tests::a_fixpoint_at_the_head_of_a_definition_is_its_function`
    /// - witness: `lower::tests::a_fixpoint_inside_a_body_is_refused_by_name`
    /// - witness: `lower::tests::a_capture_bound_by_name_is_refused_as_a_closure`
    /// - witness: `lower::tests::a_forced_native_row_in_a_body_is_its_operation`
    #[spec(ensures: |ref ret| ret.is_err() || matches!(self.function.steps.last(), Some(&(Step::Return(_) | Step::Jump { .. } | Step::Unreachable))))]
    fn body(
        &mut self,
        command: CommandId,
    ) -> Result<(), Form>
    {
        let mut command = command;
        loop {
            let node = self.arena.command(command).ok_or(Form::Dangling)?;
            let &CommandNode::Cut {
                polarity,
                producer,
                consumer,
            } = node
            else {
                return Err(Form::Outside(command_name(node)));
            };
            if let &ProducerNode::Mu { body } =
                self.arena.producer(producer).ok_or(Form::Dangling)?
            {
                // The by-name side of a negative cut against a binder suspends
                // the capture and binds it; every other cut runs it. The
                // suspended capture comes with the first closure.
                if polarity == Polarity::Negative
                    && matches!(
                        self.arena.consumer(consumer),
                        Some(&ConsumerNode::MuTilde { .. })
                    )
                {
                    return Err(Form::Closure);
                }
                self.continuations.push(Continuation::Named {
                    consumer,
                    scope: self.scope.len(),
                    continuations: self.continuations.len(),
                    floor: self.floor,
                    pending: self.pending.len(),
                    join: None,
                });
                command = body;
                continue;
            }
            let after = self.arena.consumer(consumer).ok_or(Form::Dangling)?;
            let next = match *after {
                ConsumerNode::Covariable(_)
                | ConsumerNode::MuTilde { .. }
                | ConsumerNode::Case { .. }
                | ConsumerNode::DataCase { .. } => {
                    let value = self.value(producer)?;
                    self.deliver(value, consumer)?
                },
                ConsumerNode::Destructor {
                    tag: DestructorTag::Force,
                    ref producers,
                    ref consumers,
                } => {
                    let (&[], &[frame]) = (&**producers, &**consumers)
                    else {
                        return Err(Form::Destructor);
                    };
                    if let Some(primitive) = self.forced_row(producer) {
                        self.forced(primitive, frame)?
                    }
                    else {
                        let callee_node = self.arena.producer(producer).ok_or(Form::Dangling)?;
                        let callee = match *callee_node {
                            ProducerNode::Constant(callee) => callee,
                            ProducerNode::Variable {
                                zone: Zone::Intuitionistic,
                                index,
                            } => self.itself(index).ok_or(Form::Delivery)?,
                            ProducerNode::Thunk { .. }
                            | ProducerNode::Cocase { .. }
                            | ProducerNode::Mu { .. } => {
                                return Err(Form::Closure);
                            },
                            ProducerNode::Fixpoint { .. } => return Err(Form::Fixpoint),
                            ProducerNode::Variable {
                                zone: Zone::Linear, ..
                            }
                            | ProducerNode::Literal(_)
                            | ProducerNode::Constructor { .. }
                            | ProducerNode::Primitive { .. } => {
                                return Err(Form::Delivery);
                            },
                            ProducerNode::Reify(_)
                            | ProducerNode::Decompose(_)
                            | ProducerNode::Code(_)
                            | ProducerNode::Closure { .. } => {
                                return Err(Form::Outside(producer_name(callee_node)));
                            },
                        };
                        self.call(callee, frame)?
                    }
                },
                ConsumerNode::Destructor {
                    tag: DestructorTag::Apply,
                    ..
                } => {
                    let applied = self.arena.producer(producer).ok_or(Form::Dangling)?;
                    return Err(match *applied {
                        ProducerNode::Thunk { .. }
                        | ProducerNode::Cocase { .. }
                        | ProducerNode::Mu { .. } => Form::Closure,
                        ProducerNode::Fixpoint { .. } => Form::Fixpoint,
                        ProducerNode::Variable { .. }
                        | ProducerNode::Constant(_)
                        | ProducerNode::Literal(_)
                        | ProducerNode::Constructor { .. }
                        | ProducerNode::Primitive { .. } => Form::Delivery,
                        ProducerNode::Reify(_)
                        | ProducerNode::Decompose(_)
                        | ProducerNode::Code(_)
                        | ProducerNode::Closure { .. } => Form::Outside(producer_name(applied)),
                    });
                },
                ConsumerNode::Destructor {
                    tag: DestructorTag::Project(_),
                    ..
                } => return Err(Form::Outside("DestructorTag::Project")),
                ConsumerNode::MuTildeAll { .. }
                | ConsumerNode::Select { .. }
                | ConsumerNode::ListFold { .. }
                | ConsumerNode::Top => return Err(Form::Outside(consumer_name(after))),
            };
            command = match next {
                Some(body) => body,
                None => match self.resume()? {
                    Some(body) => body,
                    None => return Ok(()),
                },
            };
        }
    }

    /// What the covariable `index` names.
    ///
    /// # Specification
    /// - ensures: the continuation at `index` from the innermost.
    /// - fails: [`Form::Unbound`] past the continuations of the function.
    /// - panics: none.
    ///
    /// # Errors
    ///
    /// As the failure clause states.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the return continuation and the name of a naming cut
    ///   are found.
    /// - witness: `lower::tests::a_let_of_a_call_with_a_call_as_its_argument_runs`
    #[spec(ensures: |ret| ret.is_ok() == usize::try_from(u32::from(index)).is_ok_and(|place| place < self.continuations.len()))]
    fn continuation(
        &self,
        index: CovariableIndex,
    ) -> Result<Continuation, Form>
    {
        let index = usize::try_from(u32::from(index)).map_err(|_overflow| Form::Unbound)?;
        self.continuations
            .iter()
            .rev()
            .nth(index)
            .copied()
            .ok_or(Form::Unbound)
    }

    /// Give `operand` to `consumer`, and give the command after it, or `None`
    /// after a return, a switch or a branch to a join.
    ///
    /// # Specification
    /// - ensures: a binder `μ̃x. s` names `operand` and gives `s`; the return
    ///   continuation returns `operand`; the covariable of a naming cut gives
    ///   `operand` to the consumer of that cut, in the scope of the cut, or
    ///   branches to the join of that cut, as [`Self::join`] states, from a
    ///   branch of a case after the cut; a case takes `operand` as
    ///   [`Self::case`] states.
    /// - fails: [`Form::Dangling`] for a node the arena does not hold;
    ///   [`Form::Unbound`] for a covariable that names nothing;
    ///   [`Form::Delivery`] for a frame, which takes no word; and as
    ///   [`Self::finish`], [`Self::join`] and [`Self::case`].
    /// - panics: none.
    /// - intension: one turn of the loop for each covariable on the way, with
    ///   no recursion.
    ///
    /// # Errors
    ///
    /// As the failure clause states.
    ///
    /// # Cost
    /// - allocation: the operand of a binder, the steps of a return, the steps
    ///   and the branches of a case, or the step and the join of a branch,
    ///   growth within the function
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the binders and the returns of the fixture, and the
    ///   name of a naming cut, each receive their operand, and the text runs.
    ///   Each branch of a case gives its answer to the binder after the case.
    /// - witness: `lower::tests::each_definition_of_the_fixture_becomes_an_object`
    /// - witness: `lower::tests::a_let_of_a_call_with_a_call_as_its_argument_runs`
    /// - witness: `lower::tests::each_branch_gives_its_answer_to_the_join_after_its_case`
    #[spec(ensures: |ref ret| ret.as_ref().map_or(true, |next| next.is_some()
        || matches!(self.function.steps.last(), Some(&(Step::Return(_) | Step::Switch { .. } | Step::Branch { .. })))))]
    fn deliver(
        &mut self,
        operand: Operand,
        consumer: ConsumerId,
    ) -> Result<Option<CommandId>, Form>
    {
        let mut consumer = consumer;
        loop {
            let node = self.arena.consumer(consumer).ok_or(Form::Dangling)?;
            match *node {
                // The binder states its type in the annotations of the
                // command arena. The lowering takes the kind of the operand.
                ConsumerNode::MuTilde { body, .. } => {
                    self.scope.push(operand);
                    return Ok(Some(body));
                },
                ConsumerNode::Covariable(index) => match self.continuation(index)? {
                    Continuation::Return => {
                        self.finish(operand)?;
                        return Ok(None);
                    },
                    Continuation::Named {
                        consumer: named,
                        scope,
                        continuations,
                        ..
                    } if self.floor <= continuations => {
                        self.scope.truncate(scope);
                        self.continuations.truncate(continuations);
                        consumer = named;
                    },
                    named @ Continuation::Named { .. } => {
                        self.join(operand, named)?;
                        return Ok(None);
                    },
                },
                ConsumerNode::Destructor { .. } => return Err(Form::Delivery),
                ConsumerNode::Case { ref arms } => return self.case(operand, arms),
                ConsumerNode::DataCase { .. } => return Err(Form::Sum),
                ConsumerNode::MuTildeAll { .. }
                | ConsumerNode::Select { .. }
                | ConsumerNode::ListFold { .. }
                | ConsumerNode::Top => return Err(Form::Outside(consumer_name(node))),
            }
        }
    }

    /// End the branch that is lowered now with a branch that gives `operand`
    /// to the join of `named`, a continuation of a naming cut outside the case
    /// of the branch.
    ///
    /// # Specification
    /// - ensures: `llvm.br` to the block of the join, with the word or the sum
    ///   of `operand`, or with no operand for the unit. The first branch to
    ///   `named` makes its join: a block whose argument has the type of
    ///   `operand`. The join waits below each block that the body of the cut
    ///   made, so it opens after each branch of each case of the cut.
    /// - fails: [`Form::Sum`] for an injection, whose layout the branch does
    ///   not know; [`Form::Delivery`] for an operand of the unit to a join of a
    ///   word, or a word to a join of the unit; [`Form::Dangling`] for an
    ///   operand that the function does not hold, or a continuation that is not
    ///   of a naming cut.
    /// - panics: none.
    ///
    /// # Errors
    ///
    /// As the failure clause states.
    ///
    /// # Cost
    /// - time: at the first branch, the shift of the blocks that wait above the
    ///   join, and one visit of each continuation
    /// - allocation: the step of the branch, and the type of the argument at
    ///   the first branch, growth within the function
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the two branches of a case of a word and of the unit
    ///   give their answers to one join, and an injection to a join is refused.
    /// - witness: `lower::tests::each_branch_gives_its_answer_to_the_join_after_its_case`
    /// - witness: `lower::tests::an_injection_to_a_join_is_refused`
    #[spec(ensures: |ref ret| ret.is_err() || matches!(self.function.steps.last(), Some(&Step::Branch { .. })))]
    fn join(
        &mut self,
        operand: Operand,
        named: Continuation,
    ) -> Result<(), Form>
    {
        let Continuation::Named {
            consumer,
            scope,
            continuations,
            floor,
            pending,
            join,
        } = named
        else {
            return Err(Form::Dangling);
        };
        let value = match operand {
            Operand::Word(value) | Operand::Sum(value) => Some(value),
            Operand::Unit => None,
            Operand::Injected { .. } => return Err(Form::Sum),
        };
        let join = match join {
            Some(join) if join.argument.is_some() == value.is_some() => join,
            Some(_) => return Err(Form::Delivery),
            None => {
                let block = Block(self.function.blocks);
                self.function.blocks = self.function.blocks.saturating_add(1);
                let (argument, bound) = match operand {
                    Operand::Word(value) | Operand::Sum(value) => {
                        let ty = self
                            .function
                            .types
                            .get(value.0)
                            .cloned()
                            .ok_or(Form::Dangling)?;
                        let argument = self.fresh(ty);
                        (
                            Some(argument),
                            if matches!(operand, Operand::Sum(_)) {
                                Operand::Sum(argument)
                            }
                            else {
                                Operand::Word(argument)
                            },
                        )
                    },
                    Operand::Unit | Operand::Injected { .. } => (None, Operand::Unit),
                };
                let join = Join { block, argument };
                let height = pending.min(self.pending.len());
                for (place, continuation) in self.continuations.iter_mut().enumerate() {
                    if let Continuation::Named {
                        pending: ref mut mark,
                        join: ref mut joined,
                        ..
                    } = *continuation
                    {
                        if place == continuations {
                            *joined = Some(join);
                        }
                        else if continuations < place && height <= *mark {
                            *mark = mark.saturating_add(1);
                        }
                    }
                }
                self.pending.insert(height, Waiting::Join {
                    join,
                    bound,
                    consumer,
                    scope,
                    continuations,
                    floor,
                });
                join
            },
        };
        self.function.steps.push(Step::Branch {
            block: join.block,
            operand: value,
        });
        Ok(())
    }

    /// Return `operand` to the return continuation.
    ///
    /// # Specification
    /// - ensures: a return of the word or the sum of `operand`, or a return
    ///   with no value for the unit. An injection gets its words first, when
    ///   the function gives a sum.
    /// - fails: [`Form::Delivery`] for an injection from a function that does
    ///   not give a sum, and as [`Self::inject`].
    /// - panics: none.
    ///
    /// # Errors
    ///
    /// As the failure clause states.
    ///
    /// # Cost
    /// - allocation: the steps of the words of an injection and of the return,
    ///   growth within the function
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the returns of the fixture, of the unit and of an
    ///   injection run, and an injection from a function of a word is refused.
    /// - witness: `lower::tests::each_definition_of_the_fixture_becomes_an_object`
    /// - witness: `lower::tests::a_definition_of_unit_returns_no_value`
    /// - witness: `lower::tests::each_branch_of_each_case_runs_and_exits_with_its_answer`
    /// - witness: `lower::tests::a_sum_with_no_layout_is_refused_by_name`
    #[spec(ensures: |ref ret| ret.is_err() || matches!(self.function.steps.last(), Some(&Step::Return(_))))]
    fn finish(
        &mut self,
        operand: Operand,
    ) -> Result<(), Form>
    {
        let value = match operand {
            Operand::Word(value) | Operand::Sum(value) => Some(value),
            Operand::Unit => None,
            Operand::Injected { summand, field } => {
                let Kind::Sum(layout) = self.function.signature.result
                else {
                    return Err(Form::Delivery);
                };
                Some(self.inject(summand, field, layout)?)
            },
        };
        self.function.steps.push(Step::Return(value));
        Ok(())
    }

    /// Write the words of the injection of `field` into `summand` of a sum of
    /// `layout`, and give the sum.
    ///
    /// # Specification
    /// - ensures: a sum in the layout [`SUM`] whose tag word holds the position
    ///   of `summand`, and whose field word holds the word of `field`, widened
    ///   to 64 bits, or 0 for the unit.
    /// - fails: [`Form::Sum`] for a summand past the second.
    /// - panics: none.
    ///
    /// # Errors
    ///
    /// As the failure clause states.
    ///
    /// # Cost
    /// - allocation: the steps and the types of the words, growth within the
    ///   function
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an injection of a byte and an injection of the unit
    ///   each reach a case of a sum in a word, and the run takes the branch of
    ///   the summand; a third summand is refused.
    /// - witness: `lower::tests::each_branch_of_each_case_runs_and_exits_with_its_answer`
    /// - witness: `lower::tests::a_sum_with_no_layout_is_refused_by_name`
    #[spec(ensures: |ref ret| ret.is_err() || ret.as_ref().is_ok_and(|&sum| matches!(self.function.types.get(sum.0), Some(&Typed::Sum(_)))))]
    fn inject(
        &mut self,
        summand: Summand,
        field: Payload,
        layout: SumLayout,
    ) -> Result<Value, Form>
    {
        let position = u64::try_from(usize::from(summand)).map_err(|_overflow| Form::Sum)?;
        if position > 1 {
            return Err(Form::Sum);
        }
        let tag = self.fresh(Typed::Word(IntegerWidth::U64));
        self.function.steps.push(Step::Constant {
            value: tag,
            literal: FixedInteger::U64(position),
        });
        let word = match field {
            Payload::Word(value) => {
                let wide = match self.function.types.get(value.0) {
                    Some(&Typed::Word(width)) => u32::from(width.bits()) == 64,
                    Some(&Typed::Sum(_)) | None => return Err(Form::Sum),
                };
                if wide {
                    value
                }
                else {
                    let widened = self.fresh(Typed::Word(IntegerWidth::U64));
                    self.function.steps.push(Step::Widen {
                        value: widened,
                        word: value,
                    });
                    widened
                }
            },
            Payload::Unit => {
                let zero = self.fresh(Typed::Word(IntegerWidth::U64));
                self.function.steps.push(Step::Constant {
                    value: zero,
                    literal: FixedInteger::U64(0),
                });
                zero
            },
        };
        let empty = self.fresh(Typed::Sum(layout));
        self.function.steps.push(Step::Undef { value: empty });
        let tagged = self.fresh(Typed::Sum(layout));
        self.function.steps.push(Step::Insert {
            value: tagged,
            sum: empty,
            word: tag,
            place: SumWord::Tag,
        });
        let sum = self.fresh(Typed::Sum(layout));
        self.function.steps.push(Step::Insert {
            value: sum,
            sum: tagged,
            word,
            place: SumWord::Field,
        });
        Ok(sum)
    }

    /// Give `operand` to the case of `arms`, and give the command after it, or
    /// `None` after a switch.
    ///
    /// # Specification
    /// - ensures: an injection takes the arm of its summand with no step, and
    ///   its field is the bound producer of the arm. A sum in a word ends the
    ///   block with a read of its tag and a switch, and each of the two arms
    ///   waits for its block, the first arm next.
    /// - fails: [`Form::Sum`] for a value that is not a sum;
    ///   [`Form::Destructor`] for an arm whose head is not the injection of its
    ///   summand, or for a count of arms other than the summands of the sum.
    /// - panics: none.
    ///
    /// # Errors
    ///
    /// As the failure clause states.
    ///
    /// # Cost
    /// - allocation: the field of an injection, or the steps of the switch and
    ///   two waiting branches, growth within the function
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a case of a parameter of a sum runs each of its two
    ///   branches, a case of an injection takes its arm with no switch, and a
    ///   case of a word is refused.
    /// - witness: `lower::tests::each_branch_of_each_case_runs_and_exits_with_its_answer`
    /// - witness: `lower::tests::a_sum_with_no_layout_is_refused_by_name`
    #[spec(ensures: |ref ret| ret.as_ref().map_or(true, |next| next.is_some()
        || matches!(self.function.steps.last(), Some(&Step::Switch { .. }))))]
    fn case(
        &mut self,
        operand: Operand,
        arms: &[PatternArm],
    ) -> Result<Option<CommandId>, Form>
    {
        let head = |place: usize| match arms.get(place) {
            Some(&PatternArm {
                constructor: ConstructorTag::Injection(summand),
                body,
            }) if usize::from(summand) == place => Ok(body),
            Some(_) | None => Err(Form::Destructor),
        };
        match operand {
            Operand::Injected { summand, field } => {
                let body = head(usize::from(summand))?;
                self.scope.push(match field {
                    Payload::Word(value) => Operand::Word(value),
                    Payload::Unit => Operand::Unit,
                });
                Ok(Some(body))
            },
            Operand::Sum(sum) => {
                let Some(&Typed::Sum(SumLayout([first_field, second_field]))) =
                    self.function.types.get(sum.0)
                else {
                    return Err(Form::Sum);
                };
                if arms.len() != 2 {
                    return Err(Form::Destructor);
                }
                let (first_body, second_body) = (head(0)?, head(1)?);
                let tag = self.fresh(Typed::Word(IntegerWidth::U64));
                self.function.steps.push(Step::Extract {
                    value: tag,
                    sum,
                    place: SumWord::Tag,
                });
                let first = Block(self.function.blocks);
                let second = Block(self.function.blocks.saturating_add(1));
                self.function.blocks = self.function.blocks.saturating_add(2);
                self.function
                    .steps
                    .push(Step::Switch { tag, first, second });
                let (scope, continuations) = (self.scope.len(), self.continuations.len());
                for (block, body, field) in [
                    (second, second_body, second_field),
                    (first, first_body, first_field),
                ] {
                    self.pending.push(Waiting::Arm(Branch {
                        block,
                        body,
                        sum,
                        field,
                        scope,
                        continuations,
                    }));
                }
                Ok(None)
            },
            Operand::Word(_) | Operand::Unit => Err(Form::Sum),
        }
    }

    /// Open the block that waits next, and give the command of its body, or
    /// `None` when no block waits.
    ///
    /// # Specification
    /// - ensures: for a branch, the label of its block, in the scope and with
    ///   the continuations of its case, then the read of the field word of the
    ///   sum, narrowed to the width of its summand, as the bound producer of
    ///   the arm. A field of the unit needs no read. For a join, the label of
    ///   its block with its argument, in the scope and with the continuations
    ///   of its cut, then the delivery of the argument to the consumer of the
    ///   cut. A join whose delivery ends its block opens the next block.
    /// - fails: as [`Self::deliver`], for a join.
    /// - panics: none.
    /// - intension: one turn of the loop for each join that ends its block.
    ///
    /// # Errors
    ///
    /// As the failure clause states.
    ///
    /// # Cost
    /// - allocation: the steps and the types of the read, and the field in the
    ///   scope, growth within the function
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the second branch of a case of `u8 + Unit` and of
    ///   `Unit + Unit` runs after the first, and reads the field of its own
    ///   summand. The join after a case runs after each branch of the case.
    /// - witness: `lower::tests::each_branch_of_each_case_runs_and_exits_with_its_answer`
    /// - witness: `lower::tests::each_branch_gives_its_answer_to_the_join_after_its_case`
    #[spec(ensures: |ref ret| ret.as_ref().map_or(true, |next| next.is_none() || self.floor <= self.continuations.len()))]
    fn resume(&mut self) -> Result<Option<CommandId>, Form>
    {
        loop {
            let branch = match self.pending.pop() {
                None => return Ok(None),
                Some(Waiting::Arm(branch)) => branch,
                Some(Waiting::Join {
                    join,
                    bound,
                    consumer,
                    scope,
                    continuations,
                    floor,
                }) => {
                    self.function.steps.push(Step::Label {
                        block: join.block,
                        argument: join.argument,
                    });
                    self.scope.truncate(scope);
                    self.continuations.truncate(continuations);
                    self.floor = floor;
                    match self.deliver(bound, consumer)? {
                        Some(next) => return Ok(Some(next)),
                        None => continue,
                    }
                },
            };
            self.function.steps.push(Step::Label {
                block: branch.block,
                argument: None,
            });
            self.scope.truncate(branch.scope);
            self.continuations.truncate(branch.continuations);
            self.floor = branch.continuations;
            let bound = match branch.field {
                Field::Unit => Operand::Unit,
                Field::Word(width) => {
                    let word = self.fresh(Typed::Word(IntegerWidth::U64));
                    self.function.steps.push(Step::Extract {
                        value: word,
                        sum: branch.sum,
                        place: SumWord::Field,
                    });
                    if u32::from(width.bits()) == 64 {
                        Operand::Word(word)
                    }
                    else {
                        let narrow = self.fresh(Typed::Word(width));
                        self.function.steps.push(Step::Narrow {
                            value: narrow,
                            word,
                        });
                        Operand::Word(narrow)
                    }
                },
            };
            self.scope.push(bound);
            return Ok(Some(branch.body));
        }
    }
}

/// Whether the body of a definition binds its own function: a recursive thunk
/// at the head of the body, the image of a fixpoint.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Recursion
{
    /// The body binds no producer outside its parameters.
    Plain,
    /// The self binder of the recursive thunk is the producer just outside the
    /// parameters. It names the function of the definition.
    Recursive,
}

/// The covariable `consumer` when it is the return continuation `0`.
///
/// # Specification
/// - ensures: `Some` exactly when `consumer` is the covariable `0`.
/// - fails: [`Form::Dangling`] for a consumer the arena does not hold.
/// - panics: none.
///
/// # Errors
///
/// As the failure clause states.
///
/// # Adequacy
/// - hypothesis: L3 — each `apply` arm of the fixture and the force of a
///   recursive thunk are cut against the covariable `0`, and the force of a
///   recursive thunk against a binder is not.
/// - witness: `lower::tests::each_definition_of_the_fixture_becomes_an_object`
/// - witness: `lower::tests::a_fixpoint_at_the_head_of_a_definition_is_its_function`
/// - witness: `lower::tests::a_fixpoint_inside_a_body_is_refused_by_name`
#[spec(ensures: |ret| ret.is_err() || ret.is_ok_and(|first| first.is_none() || matches!(arena.consumer(consumer), Some(&ConsumerNode::Covariable(index)) if u32::from(index) == 0)))]
fn first_covariable(
    arena: &CommandArena,
    consumer: ConsumerId,
) -> Result<Option<CovariableIndex>, Form>
{
    Ok(match *arena.consumer(consumer).ok_or(Form::Dangling)? {
        ConsumerNode::Covariable(index) if u32::from(index) == 0 => Some(index),
        ConsumerNode::Covariable(_)
        | ConsumerNode::MuTilde { .. }
        | ConsumerNode::MuTildeAll { .. }
        | ConsumerNode::Destructor { .. }
        | ConsumerNode::Case { .. }
        | ConsumerNode::DataCase { .. }
        | ConsumerNode::Select { .. }
        | ConsumerNode::ListFold { .. }
        | ConsumerNode::Top => None,
    })
}

/// The body of the definition `value` under one `apply` arm for each of
/// `parameters`, and whether it binds its own function.
///
/// A body `⟨fix{x; force(β) ⇒ s} |+ force(α)⟩` against the return
/// continuation `α` of the thunk is the function itself. The arms open in `s`,
/// and `x` names the function.
///
/// # Specification
/// - ensures: the command under the last arm, whose covariable `0` is the
///   return continuation. With no parameter, the body of the thunk or of its
///   recursive thunk. [`Recursion::Recursive`] exactly when the body of the
///   thunk is a recursive thunk forced against the return continuation.
/// - fails: [`Form::Dangling`] for a node the arena does not hold, and
///   [`Form::Signature`] for a value that is not a thunk, or that does not open
///   one `apply` arm against the return continuation for each parameter.
/// - panics: none.
///
/// # Errors
///
/// As the failure clause states.
///
/// # Adequacy
/// - hypothesis: L3 — the definitions of the fixture open one arm or none, a
///   definition with a parameter in its type and no arm is refused, and a
///   fixpoint at the head of a definition opens its arms under its self binder.
/// - witness: `lower::tests::each_definition_of_the_fixture_becomes_an_object`
/// - witness: `lower::tests::a_value_with_fewer_arms_than_its_type_is_refused`
/// - witness: `lower::tests::a_fixpoint_at_the_head_of_a_definition_is_its_function`
#[spec(ensures: |ret| ret.is_err() || arena.producer(value).is_some_and(|node| matches!(*node, ProducerNode::Thunk { .. })))]
fn entry(
    arena: &CommandArena,
    value: ProducerId,
    parameters: &[Kind],
) -> Result<(CommandId, Recursion), Form>
{
    let &ProducerNode::Thunk { body } = arena.producer(value).ok_or(Form::Dangling)?
    else {
        return Err(Form::Signature);
    };
    let node = arena.command(body).ok_or(Form::Dangling)?;
    let &CommandNode::Cut {
        producer, consumer, ..
    } = node
    else {
        return Err(Form::Outside(command_name(node)));
    };
    let (mut command, mut recursion) = (body, Recursion::Plain);
    if let &ProducerNode::Fixpoint { body: inner, .. } =
        arena.producer(producer).ok_or(Form::Dangling)?
        && let &ConsumerNode::Destructor {
            tag: DestructorTag::Force,
            ref producers,
            ref consumers,
        } = arena.consumer(consumer).ok_or(Form::Dangling)?
        && let (&[], &[frame]) = (&**producers, &**consumers)
        && first_covariable(arena, frame)?.is_some()
    {
        (command, recursion) = (inner, Recursion::Recursive);
    }
    for _ in parameters {
        let node = arena.command(command).ok_or(Form::Dangling)?;
        let &CommandNode::Cut {
            producer, consumer, ..
        } = node
        else {
            return Err(Form::Outside(command_name(node)));
        };
        if first_covariable(arena, consumer)?.is_none() {
            return Err(Form::Signature);
        }
        let &ProducerNode::Cocase { ref arms } = arena.producer(producer).ok_or(Form::Dangling)?
        else {
            return Err(Form::Signature);
        };
        let &[
            CopatternArm {
                destructor: DestructorTag::Apply,
                body: arm,
            },
        ] = &**arms
        else {
            return Err(Form::Signature);
        };
        command = arm;
    }
    Ok((command, recursion))
}

/// Lower each definition to one function of the `gandr` dialect.
///
/// The definition at place `n` of `definitions` is the constant at admission
/// position `n`. A call of a constant is a call of the function of its
/// definition. `types` is the core arena of the module, which holds the
/// declared type of each definition. The lowering reads no type of a node of
/// `arena`.
///
/// # Specification
/// - requires: nothing. A command that the lowering does not lay out is
///   refused.
/// - ensures: on success one function for each definition, in order, with one
///   parameter for each arrow of its signature and the operations of the table
///   of the module.
/// - provides: a [`Lowered`], which prints as the text for `compile`.
/// - fails: the [`Form`] of the first definition that the lowering refuses.
/// - panics: none.
/// - intension: one pass over the commands of each body, with no recursion.
///
/// # Errors
///
/// - [`Form::Symbol`]: a name is not a bare identifier of MLIR.
/// - [`Form::Signature`]: a type or a value is not a function of words.
/// - [`Form::Outside`]: a node or a type that the lowering has no form for, by
///   its name.
/// - Each other [`Form`]: a command of a body, as the module states.
///
/// # Cost
/// - allocation: the callees, the functions, their values, their operands and
///   their steps, growth within the size of the definitions
///
/// # Adequacy
/// - hypothesis: L3 — the five definitions of the fixture become one module,
///   which compiles to an ELF object with a symbol for each; each refusal is
///   reached by one input that breaks one rule; a node that the lowering has no
///   form for is refused by its name.
/// - witness: `lower::tests::each_definition_of_the_fixture_becomes_an_object`
/// - witness: `lower::tests::twice_calls_inc_and_jumps_to_inc`
/// - witness: `lower::tests::wrapped_gives_the_pattern_of_the_greatest_byte`
/// - witness: `lower::tests::a_name_that_is_no_identifier_is_refused`
/// - witness: `lower::tests::a_thunk_parameter_is_refused`
/// - witness: `lower::tests::a_value_with_fewer_arms_than_its_type_is_refused`
/// - witness: `lower::tests::a_variable_past_the_scope_is_unbound`
/// - witness: `lower::tests::a_thunk_inside_a_body_is_a_closure`
/// - witness: `lower::tests::a_call_with_more_arguments_than_parameters_is_refused`
/// - witness: `lower::tests::a_fixpoint_at_the_head_of_a_definition_is_its_function`
/// - witness: `lower::tests::a_fixpoint_inside_a_body_is_refused_by_name`
/// - witness: `lower::tests::a_tuple_or_a_product_with_a_component_is_refused_by_name`
/// - witness: `lower::tests::a_node_outside_the_lowering_is_refused_by_its_name`
#[spec(ensures: |ref ret| ret.as_ref().map_or(true, |lowered| lowered.functions.len() == definitions.len()))]
#[inline]
pub fn lower<'arena, 'name>(
    arena: &'arena CommandArena,
    types: &CoreArena,
    definitions: &[Definition<'name>],
) -> Result<Lowered<'name>, Form>
{
    let callees = definitions
        .iter()
        .map(|definition| {
            if bare(definition.name) == Bare(false) {
                return Err(Form::Symbol);
            }
            Ok(Callee {
                signature: signature(types, definition.signature)?,
                name: definition.name,
            })
        })
        .collect::<Result<Vec<_>, Form>>()?;
    let mut functions = Vec::with_capacity(definitions.len());
    for (position, (definition, own)) in definitions.iter().zip(&callees).enumerate() {
        let (command, recursion) = entry(arena, definition.value, &own.signature.parameters)?;
        let mut words = 0_usize;
        let scope = own
            .signature
            .parameters
            .iter()
            .map(|&kind| {
                let value = Value(words);
                match kind {
                    Kind::Word(_) => {
                        words = words.saturating_add(1);
                        Operand::Word(value)
                    },
                    Kind::Sum(_) => {
                        words = words.saturating_add(1);
                        Operand::Sum(value)
                    },
                    Kind::Unit | Kind::Void => Operand::Unit,
                }
            })
            .collect();
        let types = own
            .signature
            .parameters
            .iter()
            .filter_map(|&kind| kind.typed())
            .collect();
        let mut lowering = Lowering {
            arena,
            callees: &callees,
            function: Function {
                constant: ConstantIndex::from(position),
                name: definition.name,
                signature: own.signature.clone(),
                types,
                operands: Vec::new(),
                steps: Vec::new(),
                blocks: 0,
            },
            scope,
            recursion,
            continuations: vec![Continuation::Return],
            pending: Vec::new(),
            floor: 0,
        };
        lowering.body(command)?;
        functions.push(lowering.function);
    }
    Ok(Lowered { functions })
}
