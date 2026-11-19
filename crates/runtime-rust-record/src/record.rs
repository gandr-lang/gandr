//! The record: what the pinned toolchain answers for one request.
//!
//! A [`Record`] holds the [`Identity`] of the toolchain and the target that
//! answered, then an [`Outcome`]. A read outcome holds one [`Function`] for
//! each requested path. A refused outcome holds one [`Refusal`] for each
//! requested path that the record cannot state.
//!
//! A function's [`Staging`] is its body as THIR of the fragment that gandr
//! reads: an integer literal, a read of the parameter, `if`, `return` and a
//! call of a requested function. A body with another node stages nothing,
//! and its staging names the first such node.

use alloc::vec::Vec;
use core::fmt;

use crate::names::Available;
use crate::names::Bytes;
use crate::names::Commit;
use crate::names::FieldName;
use crate::names::FunctionPath;
use crate::names::ItemPath;
use crate::names::LlvmType;
use crate::names::Magnitude;
use crate::names::NodeIndex;
use crate::names::NodeName;
use crate::names::Symbol;
use crate::names::Target;
use crate::names::TypeName;
use crate::names::VariantName;

/// The toolchain and the target of one build.
///
/// A record holds the identity of the toolchain that wrote it, and a reader
/// refuses a record of another toolchain or of another target.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Identity
{
    /// The commit of the toolchain.
    pub commit: Commit,
    /// The target that the toolchain compiled for.
    pub target: Target,
}

impl Identity
{
    /// The toolchain that built this crate, and the target that it built
    /// for.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    #[inline]
    pub fn of_build() -> Self
    {
        Self {
            commit: Commit::from(env!("GANDR_RUST_COMMIT")),
            target: Target::from(env!("GANDR_RUST_TARGET")),
        }
    }
}

/// What the toolchain answers for one request.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Record
{
    /// The toolchain and the target that answered.
    pub identity: Identity,
    /// Each function, or each refusal.
    pub outcome: Outcome,
}

/// The functions of a request, or why the record cannot state them.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Outcome
{
    /// One function for each requested path, in the order of the request.
    Read(Vec<Function>),
    /// One refusal for each requested path that the record cannot state, in
    /// the order of the request. The list is never empty.
    Refused(Vec<Refusal>),
}

/// One function: its symbol or why it has none, and the passage and layout
/// of each operand.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Function
{
    /// The path that the request named.
    pub path: FunctionPath,
    /// The name of the function in the build's object, or why it has none.
    pub linkage: Linkage,
    /// Each argument, in declared order.
    pub arguments: Vec<Operand>,
    /// The result.
    pub result: Operand,
    /// The body as THIR of the fragment, or the first node outside it.
    pub body: Staging,
}

/// A function's body as THIR of the fragment, or why the body stages
/// nothing.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Staging
{
    /// The body, in the fragment.
    Staged(Body),
    /// The body holds a node outside the fragment.
    Outside(Outside),
}

/// A body of the fragment: each node once, each node after its children,
/// the root last.
///
/// A node names a child by its [`NodeIndex`], which is below the node's own
/// place. So the nodes form one tree, and a reader folds them in order.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Body
{
    /// The nodes, the root last.
    pub nodes: Vec<Node>,
}

/// One node of THIR in the fragment.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Node
{
    /// An integer literal.
    Literal(Literal),
    /// A read of the function's one parameter.
    Parameter,
    /// `if condition { then } else { otherwise }`.
    If
    {
        /// The condition.
        condition: NodeIndex,
        /// The arm that runs when the condition is true.
        then: NodeIndex,
        /// The arm that runs when the condition is false.
        otherwise: NodeIndex,
    },
    /// `return value`.
    Return(NodeIndex),
    /// A call of a requested function at one argument.
    Call
    {
        /// The requested function that the call names.
        callee: FunctionPath,
        /// The argument.
        argument: NodeIndex,
    },
}

/// An integer literal: its sign and its magnitude.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Literal
{
    /// Whether the literal is negated.
    pub sign: Sign,
    /// The literal's digits as a number.
    pub magnitude: Magnitude,
}

/// The sign of an integer literal.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Sign
{
    /// The literal as written.
    Plus,
    /// The literal under a unary minus.
    Minus,
}

/// Why a body stages nothing.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Outside
{
    /// The body holds a node of this kind, which the fragment lacks.
    Node(NodeName),
    /// The body calls an item that the request does not hold.
    Callee(ItemPath),
    /// The body holds more nodes than [`Body::CEILING`].
    Large,
}

impl Body
{
    /// The most nodes that a staged body holds. A body with more stages
    /// nothing, so a staged body's bytes stay bounded.
    ///
    /// economy: 4096 nodes is past each body of the fragment that the
    /// corpus holds, whose largest is 10 nodes. A larger ceiling waits for a
    /// measured body of the general fragment that #327 owes.
    pub const CEILING: usize = 4096;
}

/// The name of a function in the build's object, or why the object holds no
/// name for it.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Linkage
{
    /// The function's symbol under the v0 mangling.
    Symbol(Symbol),
    /// The object holds no symbol of the function.
    Absent(Absence),
}

/// Why the build's object holds no symbol of a function.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Absence
{
    /// The build copies the function into each caller and emits no body of
    /// its own. A consumer that links by symbol refuses the function, and a
    /// consumer that takes the function's address makes the build keep a
    /// body.
    Inlined,
}

/// One argument or the result: how it passes and how its type is laid out.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Operand
{
    /// How the operand passes under the build's convention.
    pub passage: Passage,
    /// The layout of the operand's type.
    pub layout: Layout,
}

/// How an operand passes under the convention that rustc computes for the
/// build.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Passage
{
    /// The operand has no size, and no operand passes.
    Ignore,
    /// The operand passes as one LLVM value of its own type.
    Direct(Part),
    /// The operand's two scalars pass as two LLVM values.
    Pair(Part, Part),
    /// The operand's bytes pass as one LLVM value of another type.
    Cast(Part),
    /// The operand passes behind an address. A result passes behind an
    /// address that the caller gives first, and the function returns
    /// nothing.
    Indirect(Part),
    /// The operand passes behind an address, and the callee finds its copy
    /// on the stack: LLVM's `byval`.
    OnStack(Part),
}

/// One LLVM value of a passage: its type and its extension.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Part
{
    /// The LLVM type of the value.
    pub ty: LlvmType,
    /// How the caller widens the value to its register.
    pub extension: Extension,
}

/// How the caller widens a narrow integer to its register.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Extension
{
    /// The value passes as it is.
    Plain,
    /// The value passes zero-extended: LLVM's `zeroext`.
    Zero,
    /// The value passes sign-extended: LLVM's `signext`.
    Sign,
}

/// A type's layout as rustc computes it: size, stride, alignment, the offset
/// of each field and the niche.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Layout
{
    /// The type, as rustc prints it.
    pub ty: TypeName,
    /// The size.
    pub size: Bytes,
    /// The distance between two values of the type in an array.
    pub stride: Bytes,
    /// The alignment that the convention requires.
    pub align: Bytes,
    /// The largest niche of the type.
    pub niche: Niche,
    /// The fields, or the variants and their fields.
    pub shape: Shape,
}

/// The largest run of invalid values of a scalar in a type.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Niche
{
    /// Each bit pattern of the type is valid.
    None,
    /// The scalar at an offset has invalid values.
    At
    {
        /// The offset of the scalar.
        offset: Bytes,
        /// The size of the scalar.
        width: Bytes,
        /// How many values of the scalar are invalid.
        available: Available,
    },
}

/// The fields of a type.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Shape
{
    /// A scalar, with no fields.
    Scalar,
    /// A struct or a tuple: each field in declared order.
    Struct(Vec<Field>),
    /// An enum: where it keeps its variant, and each variant's fields.
    Enum
    {
        /// Where the enum keeps which variant it holds.
        discriminant: Discriminant,
        /// Each variant that the layout holds, in declared order.
        arms: Vec<Arm>,
    },
}

/// One field and its offset.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Field
{
    /// The field's name.
    pub name: FieldName,
    /// The field's offset from the start of the value.
    pub offset: Bytes,
}

/// Where an enum keeps which variant it holds.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Discriminant
{
    /// One variant holds each value, so nothing is kept.
    Unneeded,
    /// In the invalid values of the scalar at an offset.
    Niche
    {
        /// The offset of the scalar.
        offset: Bytes,
    },
    /// In a tag of a size at an offset.
    Tag
    {
        /// The offset of the tag.
        offset: Bytes,
        /// The size of the tag.
        size: Bytes,
    },
}

/// One variant and the offset of each of its fields.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Arm
{
    /// The variant's name.
    pub name: VariantName,
    /// Each field in declared order.
    pub fields: Vec<Field>,
}

/// Why the record cannot state a requested function.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Refusal
{
    /// The function has a generic parameter, so it has no one convention.
    Generic(FunctionPath),
    /// The function is not reachable from outside its crate.
    NotPublic(FunctionPath),
    /// The crate has no function at the path.
    Missing(FunctionPath),
    /// The record does not state the layout or the passage of a type of the
    /// function's signature.
    Unstated
    {
        /// The function.
        function: FunctionPath,
        /// The type.
        ty: TypeName,
        /// What the record cannot state about the type.
        why: Unstatable,
    },
}

/// What the record cannot state about a type.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Unstatable
{
    /// The type has no size that the build knows.
    Unsized,
    /// The type has no value.
    Uninhabited,
    /// The type is an array.
    Array,
    /// The type is a union.
    Union,
    /// The type passes in a way that the record has no form for.
    Passage,
}

impl fmt::Display for Refusal
{
    /// Names the function and the cause of the refusal.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: writes the function's path, then the cause by its name.
    /// - provides: the line a refusal reports.
    /// - fails: propagates the formatter's own write failure unchanged.
    /// - panics: none.
    /// - executable: none — the formatter exposes no readable output buffer.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each refusal renders its function and its cause.
    /// - witness: `tests::each_refusal_names_its_function_and_its_cause`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            Self::Generic(ref path) => write!(
                f,
                "`{path}` is generic: the record states a function with no generic parameter"
            ),
            Self::NotPublic(ref path) => write!(
                f,
                "`{path}` is not public: no caller outside its crate reaches it"
            ),
            Self::Missing(ref path) => write!(
                f,
                "`{path}` is missing: the crate has no function at this path"
            ),
            Self::Unstated {
                ref function,
                ref ty,
                why,
            } => {
                let cause = match why {
                    Unstatable::Unsized => "it has no size",
                    Unstatable::Uninhabited => "it has no value",
                    Unstatable::Array => "it is an array",
                    Unstatable::Union => "it is a union",
                    Unstatable::Passage => "its passage has no form in the record",
                };
                write!(
                    f,
                    "`{function}` is unstated: the record does not state `{ty}`, since {cause}"
                )
            },
        }
    }
}
