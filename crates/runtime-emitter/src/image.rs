//! A closed command's canonical bytes, and their read into a fresh arena.
//!
//! [`encode`] writes the command that a root reaches, with the definitions
//! that it unfolds. [`read`] mints the bytes into a fresh arena and judges
//! the root again with [`check_command`].
//!
//! A run takes commands of the sequent IL, and an arena holds them by index.
//! An index holds inside one process alone, so a checked program cannot leave
//! the process in a form that runs. The image names no index of the source
//! arena. Each node stands once, after each child that it names, in the order
//! in which a walk from the root completes the nodes. A child is named by its
//! position among the nodes of its family before it. So equal commands give
//! equal bytes, and the reader mints each node over children that it holds.
//!
//! The bytes are one value of the value plane, in its flat form
//! ([`gandr_storage_values::encode_flat`]): the image's open, five counts, the
//! table of annotations when the nodes name one, the nodes, the definitions,
//! and the close.
//!
//! |Record|Words after the open|
//! |---|---|
//! |the image|the producers, the consumers, the commands, the definitions and the root's position|
//! |the image with annotations|as the image, then the count of roots and the bytes of the table|
//! |a node|its form's payload, each child as its family position, each annotation as the ordinal of its root|
//! |a definition|the constant, then zero for an opaque one or one past its body's position|
//!
//! # Boundaries
//!
//! - **Annotations cross as content.** A code, a fold, an operation, a handler
//!   and a session action name core nodes of the arena's annotations. Their
//!   roots form one content table in the node codec of `gandr-core-content`,
//!   one place for each distinct content. The reader mints the table into the
//!   fresh arena before the nodes that name it. A command that names no
//!   annotation has no table, so its bytes are the image's bytes alone.
//! - **A digest admits nothing.** A content pointer of the bytes names them.
//!   The kernel's admission stays the one authority of validity, so [`read`]
//!   runs [`check_command`] on each root that it mints.
//! - **Sharing inside one command is kept.** A node that two parents name is
//!   written once. Two commands share no node.
//! - **The order is not checked.** The reader mints what it can mint. It does
//!   not refuse bytes whose order a walk would not give.
//!
//! # References
//!
//! - `vault:01a1e7b4-8c77-7a81-9165-ff37ea870424` — lineage: the IO direction,
//!   § io-direction-first-crate: the byte form of the commands that an embedded
//!   program runs, judged again where it is read.

use alloc::borrow::Cow;
use alloc::boxed::Box;
use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::sync::Arc;
use alloc::vec::Vec;
use core::fmt;

use gandr_core_content::ArenaNode;
use gandr_core_content::NodeIndex;
use gandr_core_content::codec::CodecError;
use gandr_core_content::codec::Reader as NodeReader;
use gandr_core_content::codec::Writer as NodeWriter;
use gandr_core_content::codec::read_effect_signature;
use gandr_core_content::codec::read_session_action;
use gandr_core_content::codec::write_effect_signature;
use gandr_core_content::codec::write_session_action;
use gandr_core_content::seating;
use gandr_core_sequent::CheckRefusal;
use gandr_core_sequent::CommandArena;
use gandr_core_sequent::CommandId;
use gandr_core_sequent::CommandNode;
use gandr_core_sequent::ConstructorTag as Head;
use gandr_core_sequent::ConsumerId;
use gandr_core_sequent::ConsumerNode;
use gandr_core_sequent::CopatternArm;
use gandr_core_sequent::CovariableIndex;
use gandr_core_sequent::Definition;
use gandr_core_sequent::Definitions;
use gandr_core_sequent::DestructorTag;
use gandr_core_sequent::FreeSet;
use gandr_core_sequent::Independence;
use gandr_core_sequent::Introduces;
use gandr_core_sequent::MarkRefusal;
use gandr_core_sequent::MintRefusal;
use gandr_core_sequent::NodeAddress;
use gandr_core_sequent::PatternArm;
use gandr_core_sequent::ProducerArity;
use gandr_core_sequent::ProducerId;
use gandr_core_sequent::ProducerNode;
use gandr_core_sequent::Route;
use gandr_core_sequent::Selector;
use gandr_core_sequent::check_command;
use gandr_core_sequent::command_annotations;
use gandr_core_sequent::command_children;
use gandr_core_sequent::consumer_annotations;
use gandr_core_sequent::consumer_children;
use gandr_core_sequent::producer_children;
use gandr_core_term::FieldLabel;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_core_term::control::EffectClause;
use gandr_core_term::control::StackFrame;
use gandr_core_term::effect::EffectOp;
use gandr_core_term::effect::EffectSig;
use gandr_core_term::effect::OperationName;
use gandr_core_term::memory::AccessMode;
use gandr_core_term::memory::HoldGrade;
use gandr_core_term::memory::MemoryForm;
use gandr_core_term::memory::Place;
use gandr_core_term::primitive::Arguments;
use gandr_core_term::primitive::PRELUDE;
use gandr_core_term::session::ChildOrder;
use gandr_core_term::session::SessionAction;
use gandr_core_term::world::World;
use gandr_core_term::world::WorldForm;
use gandr_kernel_term::Component;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::FieldCount;
use gandr_kernel_term::FixpointEvidence;
use gandr_kernel_term::JointPositions;
use gandr_kernel_term::StagedPosition;
use gandr_storage_values::CanonicalValue;
use gandr_storage_values::CanonicalWord;
use gandr_storage_values::ChunkStore;
use gandr_storage_values::ConstructorTag;
use gandr_storage_values::DecodeWork;
use gandr_storage_values::EmissionFault;
use gandr_storage_values::FlatBytes;
use gandr_storage_values::TokenBody;
use gandr_storage_values::TokenBytes;
use gandr_storage_values::TokenReader;
use gandr_storage_values::TokenSink;
use gandr_storage_values::ValueError;
use gandr_storage_values::decode_flat;
use gandr_storage_values::encode_flat;
use gandr_theory_cell_complexes::Polarity;
use quenchant_shape::shape::Maybe;

mod annotations;

use crate::crossing::Opened;
use crate::crossing::emit_head;
use crate::crossing::emit_literal;
use crate::crossing::read_head;
use crate::crossing::read_literal;

/// The most nodes, and the highest constant, that one image may state: the
/// reader refuses a count past it before it reads a node.
///
/// A caller with a tighter bound checks the counts that [`Read`] answers.
const MOST: u64 = 1_u64 << 24_u32;

/// The image: five counts, then the nodes and the definitions.
const IMAGE: u8 = 0x01_u8;

/// A definition: its constant, then zero or one past its body's position.
const DEFINITION: u8 = 0x02_u8;

/// A first-class stack: its frame count, then each frame's kind and operand.
const REIFY: u8 = 0x20_u8;

/// A primitive: its row in the prelude, its argument count and its arguments.
const PRIMITIVE: u8 = 0x21_u8;

/// A decomposition: the dialogue's producer.
const DECOMPOSE: u8 = 0x22_u8;

/// A variable: its zone and its index.
const VARIABLE: u8 = 0x23_u8;

/// A constant: its admission position.
const CONSTANT: u8 = 0x24_u8;

/// A literal: the literal as a crossing writes it.
const LITERAL: u8 = 0x25_u8;

/// A constructor: its head as a crossing writes it, then its producer fields
/// and its consumer fields, each list after its count.
const CONSTRUCTOR: u8 = 0x26_u8;

/// A thunk: its body.
const THUNK: u8 = 0x27_u8;

/// A recursive thunk: its body, then its evidence.
const FIXPOINT: u8 = 0x28_u8;

/// A copattern object: its arm count, then each arm's head and body.
const COCASE: u8 = 0x29_u8;

/// A closure: its environment's count and values, then its code.
const CLOSURE: u8 = 0x2a_u8;

/// A context capture: its body.
const MU: u8 = 0x2b_u8;

/// A covariable: its index.
const COVARIABLE: u8 = 0x40_u8;

/// A value binder: its independence, then its body.
const MU_TILDE: u8 = 0x41_u8;

/// A binder of several values: its arity, then its body.
const MU_TILDE_ALL: u8 = 0x42_u8;

/// A destructor frame: its head, then its producer arguments and its consumer
/// arguments, each list after its count.
const DESTRUCTOR: u8 = 0x43_u8;

/// A pattern match: its arm count, then each arm's head as a crossing writes
/// it and its body.
const CASE: u8 = 0x44_u8;

/// A nominal match: its branches and its arities, each list after its count,
/// then its continuation.
const DATA_CASE: u8 = 0x45_u8;

/// A selection: its selector, then its continuation.
const SELECT: u8 = 0x46_u8;

/// The terminal consumer.
const TOP: u8 = 0x47_u8;

/// A resumption: its stack, its body and its continuation.
const RESUME: u8 = 0x60_u8;

/// An abandonment: its stack and its continuation.
const ABANDON: u8 = 0x61_u8;

/// An answer delimiter: its body and its continuation.
const RESET: u8 = 0x62_u8;

/// A capture to the nearest delimiter: its body and its continuation.
const SHIFT: u8 = 0x63_u8;

/// A cut: its polarity, its producer and its consumer.
const CUT: u8 = 0x64_u8;

/// A delivery: its producers after their count, then its consumer.
const DELIVER: u8 = 0x65_u8;

/// A memory form: its case and the case's operands, then its continuation.
const MEMORY: u8 = 0x66_u8;

/// A world form: its case and the case's operands, then its continuation.
const WORLD: u8 = 0x67_u8;

/// A code. Its form is owed, so the reader refuses it.
const CODE: u8 = 0x2c_u8;

/// A fold. Its form is owed, so the reader refuses it.
const LIST_FOLD: u8 = 0x48_u8;

/// An operation request. Its form is owed, so the reader refuses it.
const PERFORM: u8 = 0x68_u8;

/// A handler. Its form is owed, so the reader refuses it.
const HANDLE: u8 = 0x69_u8;

/// A session action. Its form is owed, so the reader refuses it.
const SESSION: u8 = 0x6a_u8;

/// The tag of an image whose nodes name annotations: its counts, its table
/// of annotations, then its nodes.
const ANNOTATED: u8 = 0x03_u8;

/// A node form that the image does not write.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Uncodable
{
    /// A constructor's head that does not cross: a recorded run, a dialogue
    /// or a web.
    Head(crate::crossing::Uncrossable),
}

/// Why a command has no image, or why bytes give no command.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ImageRefusal
{
    /// A node that the root reaches has a form that the image does not
    /// write.
    Uncodable
    {
        /// The node in the source arena.
        node: NodeAddress,
        /// Its form.
        form: Uncodable,
    },
    /// The source arena holds no node at an address that the root reaches.
    Dangling(NodeAddress),
    /// The definitions hold no entry for a constant that the command names.
    Undefined(ConstantIndex),
    /// The value plane refused the bytes: a tag that no node has, a payload
    /// that its form does not write, a count past the reader's ceiling, a
    /// truncated stream or bytes after the image.
    Plane(ValueError),
    /// The bytes state two definitions of one constant.
    Defined(ConstantIndex),
    /// The fresh arena refused a node: a child that stands after its parent,
    /// or a family past its ceiling.
    Mint(MintRefusal),
    /// The fresh arena refused an independence mark.
    Mark(MarkRefusal),
    /// The minted root does not check.
    Check(CheckRefusal),
    /// The minted root checks with free variables, so it is not closed.
    Open(FreeSet),
    /// The node codec refused the bytes of the table of annotations, of a
    /// signature or of a session action: a child that names a node after it,
    /// a table that its roots do not number by discovery, or bytes that no
    /// table writes.
    Table(CodecError),
    /// A root of the table does not mint into the fresh arena's annotations,
    /// or a node names a root that the table does not hold or that has
    /// another sort.
    Annotation(seating::Absent),
}

impl From<ValueError> for ImageRefusal
{
    /// The value plane's refusal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(error: ValueError) -> Self
    {
        Self::Plane(error)
    }
}

impl From<MintRefusal> for ImageRefusal
{
    /// The fresh arena's refusal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(refusal: MintRefusal) -> Self
    {
        Self::Mint(refusal)
    }
}

impl fmt::Display for ImageRefusal
{
    /// Names the refusal and its subject.
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
            Self::Uncodable {
                node,
                form: Uncodable::Head(_),
            } => write!(
                f,
                "the node {node} is a constructor of a head that does not cross, which the image \
                 does not write"
            ),
            Self::Dangling(node) => write!(f, "the arena holds no node {node}"),
            Self::Undefined(constant) => {
                write!(f, "constant {} has no definition", usize::from(constant))
            },
            Self::Plane(ref error) => write!(f, "the bytes are refused: {error}"),
            Self::Defined(constant) => {
                write!(f, "constant {} has two definitions", usize::from(constant))
            },
            Self::Mint(refusal) => write!(f, "a node is refused: {refusal}"),
            Self::Mark(refusal) => write!(f, "a mark is refused: {refusal}"),
            Self::Check(ref refusal) => write!(f, "the root does not check: {refusal}"),
            Self::Open(_) => f.write_str("the root has free variables"),
            Self::Table(error) => {
                f.write_str("the table of annotations is refused: ")?;
                f.write_str(match error {
                    CodecError::Corrupt => "bytes that no table writes",
                    CodecError::NonCanonical => "bytes that are not the one form of their table",
                    CodecError::LevelOffsetTooLarge { .. } => "a level past the cap of the reader",
                    CodecError::Unsupported(_) => "a form that has no byte form",
                    CodecError::Unrepresentable => "a count or a length past its word",
                })
            },
            Self::Annotation(reason) => {
                f.write_str("an annotation does not mint: ")?;
                f.write_str(match reason {
                    seating::Absent::Unresolved => "an id of another arena",
                    seating::Absent::Cyclic => "a node that is its own descendant",
                    seating::Absent::Unplaced => {
                        "a root or a constant that the image does not hold"
                    },
                    seating::Absent::IllSorted => "a root of another sort",
                    seating::Absent::Unseatable => "an item with no seat",
                    seating::Absent::Unplaceable => "an index past its space",
                    seating::Absent::Unwalked => "a place past the walk",
                })
            },
        }
    }
}

impl core::error::Error for ImageRefusal
{
}

/// A command read from its image: a fresh arena, the definitions that the
/// command unfolds, and its root there.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug)]
pub struct Read
{
    /// The fresh arena, which holds the command's nodes and nothing else.
    pub arena: CommandArena,
    /// The definitions, an opaque entry at each position that the command
    /// does not name.
    pub definitions: Definitions,
    /// The root.
    pub root: CommandId,
}

/// Write the canonical bytes of the command `root` in `arena`, with each
/// definition in `definitions` that it unfolds.
///
/// # Specification
/// - requires: nothing; a command that the image does not write is refused.
/// - ensures: on success the flat bytes of one image value. Two commands whose
///   reachable nodes and definitions are equal give equal bytes, whatever their
///   arenas hold besides.
/// - fails: as the errors state, before any byte is written.
/// - panics: none.
/// - executable: none — equality of the bytes is the round trip's, which needs
///   [`read`].
///
/// # Errors
/// [`ImageRefusal::Uncodable`] naming the first node in walk order whose head
/// does not cross; [`ImageRefusal::Dangling`] for an address the arena does
/// not hold; [`ImageRefusal::Undefined`] for a constant with no definition;
/// [`ImageRefusal::Table`] for an annotation that the node codec does not
/// write; [`ImageRefusal::Plane`] for the plane's refusal of the emission.
///
/// # Adequacy
/// - hypothesis: L2 — each named program reads back, checks, and runs to its
///   first command's outcome on both tiers; two focus runs of one source give
///   equal bytes. L3 — a code reads back to equal bytes, and a root past its
///   table and bytes past the table are each refused by name.
/// - witness: `tests::image::each_named_program_reads_back_and_runs_alike`
/// - witness: `tests::image::two_focuses_give_equal_bytes`
/// - witness: `tests::image::a_code_round_trips_and_a_fault_of_its_table_is_refused_by_name`
///
/// # Cost
/// - allocation: the walk's order and its slots, growth within the command
#[inline]
pub fn encode(
    arena: &CommandArena,
    definitions: &Definitions,
    root: CommandId,
) -> Result<FlatBytes, ImageRefusal>
{
    Ok(encode_flat(&Image::of(arena, definitions, root)?)?)
}

/// Read the command that `body` writes into a fresh arena, and judge its
/// root again.
///
/// # Specification
/// - requires: nothing; bytes that give no closed, checked command are refused.
/// - ensures: on success a fresh arena holding one node per node that the bytes
///   write, the definitions that they state, and the root, which
///   [`check_command`] admits with no free variable.
/// - fails: as the errors state; the fresh arena is dropped.
/// - panics: none.
/// - executable: none — the check is the postcondition, and it runs.
///
/// # Errors
/// [`ImageRefusal::Plane`] for a tag that no node has, a payload that its
/// form does not write, a count past the ceiling, a truncated stream and
/// bytes after the image; [`ImageRefusal::Defined`] for a constant defined
/// twice; [`ImageRefusal::Mint`] for a child after its parent;
/// [`ImageRefusal::Mark`] for a mark on a node that is not a binder;
/// [`ImageRefusal::Check`] and [`ImageRefusal::Open`] for a root that does
/// not check closed; [`ImageRefusal::Table`] for a table of annotations that
/// the node codec refuses; [`ImageRefusal::Annotation`] for an annotation
/// that does not mint.
///
/// # Adequacy
/// - hypothesis: L2 — as [`encode`]. L3 — a tag that no node has, a child after
///   its parent, a count past the ceiling, bytes after the image, a root past
///   its table and bytes past the table are each refused by name.
/// - witness: `tests::image::each_named_program_reads_back_and_runs_alike`
/// - witness: `tests::image::each_fault_of_the_bytes_is_refused_by_name`
/// - witness: `tests::image::a_code_round_trips_and_a_fault_of_its_table_is_refused_by_name`
///
/// # Cost
/// - allocation: the nodes and the fresh arena, growth within the image
#[inline]
pub fn read(body: TokenBody<'_>) -> Result<Read, ImageRefusal>
{
    let image: Image<'static> = decode_flat(body)?;
    image.mint()
}

/// One node of an image, borrowed from its source arena or read.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug)]
enum Node<'arena>
{
    /// A producer.
    Producer(Cow<'arena, ProducerNode>),
    /// A consumer, with the independence of a value binder.
    Consumer(Cow<'arena, ConsumerNode>, Independence),
    /// A command.
    Command(Cow<'arena, CommandNode>),
    /// A read node that names annotations, before the table is minted.
    Pending(Pending),
}

/// A read node that names annotations: each annotation as the ordinal of its
/// root in the table, and a signature or an action as the bytes of the node
/// codec, which [`Image::mint`] reads once the table is minted.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug)]
enum Pending
{
    /// A code.
    Code(Word32),
    /// A fold over a list.
    ListFold
    {
        /// The ordinal of the element type.
        element: Word32,
        /// The ordinal of the result type.
        result: Word32,
        /// The nil branch.
        on_nil: CommandId,
        /// The cons branch.
        on_cons: CommandId,
        /// The continuation.
        continuation: ConsumerId,
    },
    /// An operation request.
    Perform
    {
        /// The interface, over ordinals.
        signature: annotations::Buffer,
        /// The operation.
        operation: OperationName,
        /// The route.
        route: Route,
        /// The payload.
        payload: ProducerId,
        /// The continuation.
        continuation: ConsumerId,
    },
    /// A handler.
    Handle
    {
        /// The interface, over ordinals.
        signature: annotations::Buffer,
        /// Whether the handler introduces a capability.
        introduces: Introduces,
        /// The handled command.
        subject: CommandId,
        /// The return clause.
        on_return: CommandId,
        /// The operation clauses.
        clauses: Arc<[EffectClause<CommandId>]>,
        /// The continuation.
        continuation: ConsumerId,
    },
    /// A session action.
    Session
    {
        /// The action, over positions and ordinals.
        action: annotations::Buffer,
        /// The continuation.
        continuation: ConsumerId,
    },
}

/// How an image names a child: by its position among the nodes of its family
/// before it.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug)]
enum Numbering
{
    /// The nodes were read, so an id is its position already.
    Read,
    /// The nodes are borrowed, so each id maps to the position it takes.
    Taken
    {
        /// Each producer's position.
        producers: BTreeMap<ProducerId, u32>,
        /// Each consumer's position.
        consumers: BTreeMap<ConsumerId, u32>,
        /// Each command's position.
        commands: BTreeMap<CommandId, u32>,
    },
}

/// The refusal of an emission that names a node the image did not take. The
/// image takes each node that it names, so no emission meets it.
///
/// # Specification
/// trivial.
const fn untaken() -> ValueError
{
    ValueError::MalformedEmission {
        fault: EmissionFault::PayloadOutsideConstructor,
    }
}

impl Numbering
{
    /// The position of a producer.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// [`untaken`] for a producer that the image did not take.
    fn producer(
        &self,
        id: ProducerId,
    ) -> Result<CanonicalWord, ValueError>
    {
        match *self {
            Self::Read => Ok(position(u32::from(id))),
            Self::Taken { ref producers, .. } => producers
                .get(&id)
                .map(|&at| position(at))
                .ok_or_else(untaken),
        }
    }

    /// The position of a consumer.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// [`untaken`] for a consumer that the image did not take.
    fn consumer(
        &self,
        id: ConsumerId,
    ) -> Result<CanonicalWord, ValueError>
    {
        match *self {
            Self::Read => Ok(position(u32::from(id))),
            Self::Taken { ref consumers, .. } => consumers
                .get(&id)
                .map(|&at| position(at))
                .ok_or_else(untaken),
        }
    }

    /// The position of a command.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// [`untaken`] for a command that the image did not take.
    fn command(
        &self,
        id: CommandId,
    ) -> Result<CanonicalWord, ValueError>
    {
        match *self {
            Self::Read => Ok(position(u32::from(id))),
            Self::Taken { ref commands, .. } => commands
                .get(&id)
                .map(|&at| position(at))
                .ok_or_else(untaken),
        }
    }
}

/// A position among the nodes of one family, or an index that a node holds
/// in 32 bits.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[repr(transparent)]
struct Word32(u32);

/// A count, an ordinal or a constant that the host's counts hold.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[repr(transparent)]
struct Ordinal(usize);

/// How many cases a word names, from zero.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[repr(transparent)]
struct Choices(u64);

/// The case that a word names, below its [`Choices`].
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[repr(transparent)]
struct Case(u64);

/// Implements `From<Word32>` for each id that a node names in 32 bits.
macro_rules! from_word {
    ($($id:ty),*) => {$(
        impl From<Word32> for $id
        {
            /// The id at the position.
            ///
            /// # Specification
            /// trivial.
            #[inline]
            fn from(word: Word32) -> Self
            {
                Self::from(word.0)
            }
        }
    )*};
}

from_word!(
    ProducerId,
    ConsumerId,
    CommandId,
    CovariableIndex,
    DeBruijnIndex
);

/// Implements `From<Ordinal>` for each count that a node holds.
macro_rules! from_ordinal {
    ($($count:ty),*) => {$(
        impl From<Ordinal> for $count
        {
            /// The count of the ordinal.
            ///
            /// # Specification
            /// trivial.
            #[inline]
            fn from(ordinal: Ordinal) -> Self
            {
                Self::from(ordinal.0)
            }
        }
    )*};
}

from_ordinal!(
    ConstantIndex,
    Component,
    StagedPosition,
    FieldCount,
    ProducerArity
);

/// A position as the plane's word.
///
/// # Specification
/// trivial.
fn position<At>(at: At) -> CanonicalWord
where
    u32: From<At>,
{
    CanonicalWord::from(u64::from(u32::from(at)))
}

/// A count or an ordinal as the plane's word.
///
/// # Specification
/// trivial.
///
/// # Errors
/// [`untaken`] for a count wider than a word, which no host this crate builds
/// for has.
fn count<Count>(count: Count) -> Result<CanonicalWord, ValueError>
where
    u64: TryFrom<Count>,
{
    u64::try_from(count)
        .map(CanonicalWord::from)
        .map_err(|_wider| untaken())
}

/// A closed command's image: its nodes in completion order, its definitions
/// and its root.
///
/// # Specification
/// - executable: none — a data type; [`encode`] and [`read`] state it.
#[derive(Clone, Debug)]
struct Image<'arena>
{
    /// The nodes, each after each child that it names.
    nodes: Vec<Node<'arena>>,
    /// How the nodes name their children.
    numbering: Numbering,
    /// The nodes of each family: producers, consumers, commands.
    counts: [u32; 3],
    /// Each constant that the command names, in the order the walk met it,
    /// with its definition, a body by its position.
    definitions: Vec<(ConstantIndex, Definition)>,
    /// The root's position.
    root: CommandId,
    /// The table of the annotations that the nodes name.
    annotations: Annotations,
}

/// The table of a command's annotations, as the image writes it.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Default)]
struct Annotations
{
    /// The number of roots, zero for a command that names none.
    roots: usize,
    /// The bytes of the table, in the node codec of `gandr-core-content`.
    bytes: annotations::Buffer,
    /// The ordinal of each root, for a walk; empty for a read.
    ordinals: BTreeMap<ArenaNode, Word32>,
}

/// The state of one walk from a root.
///
/// # Specification
/// trivial.
struct Walk<'arena>
{
    /// The source arena.
    arena: &'arena CommandArena,
    /// The nodes taken so far.
    nodes: Vec<Node<'arena>>,
    /// The positions taken so far.
    producers: BTreeMap<ProducerId, u32>,
    /// The positions taken so far.
    consumers: BTreeMap<ConsumerId, u32>,
    /// The positions taken so far.
    commands: BTreeMap<CommandId, u32>,
    /// The constants met, in order.
    met: Vec<ConstantIndex>,
    /// The constants met, for a test of membership.
    seen: BTreeSet<ConstantIndex>,
    /// The nodes owed, each with whether its children are pushed.
    pending: Vec<(NodeAddress, bool)>,
    /// The children of one node, in order.
    children: Vec<NodeAddress>,
    /// The roots of the annotations, in the order the walk met them.
    roots: Vec<ArenaNode>,
    /// The ordinal of each root.
    ordinals: BTreeMap<ArenaNode, Word32>,
}

impl Walk<'_>
{
    /// The position that `node` took, if it took one.
    ///
    /// # Specification
    /// trivial.
    fn taken(
        &self,
        node: NodeAddress,
    ) -> Option<Word32>
    {
        match node {
            NodeAddress::Producer(id) => self.producers.get(&id).copied().map(Word32),
            NodeAddress::Consumer(id) => self.consumers.get(&id).copied().map(Word32),
            NodeAddress::Command(id) => self.commands.get(&id).copied().map(Word32),
        }
    }

    /// Take every node that `root` reaches and that no earlier walk took,
    /// each after its children, and answer the position `root` took.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success each node that `root` reaches stands in the nodes
    ///   once, after each child that it names, in the order in which a walk
    ///   that visits the children in order completes them; each constant that a
    ///   taken producer names is met.
    /// - fails: the first node in walk order that the arena does not hold or
    ///   whose form the image does not write.
    /// - panics: none.
    /// - executable: none — the walk is its own specification.
    /// - intension: an explicit worklist, so a deep command needs no deep
    ///   stack.
    ///
    /// # Errors
    /// [`ImageRefusal::Dangling`] and [`ImageRefusal::Uncodable`].
    ///
    /// # Adequacy
    /// - hypothesis: L2 — as [`encode`].
    /// - witness: `tests::image::each_named_program_reads_back_and_runs_alike`
    ///
    /// # Cost
    /// - allocation: the worklist, the nodes and the positions, growth within
    ///   the command
    fn take(
        &mut self,
        root: NodeAddress,
    ) -> Result<Word32, ImageRefusal>
    {
        self.pending.push((root, false));
        while let Some((node, expanded)) = self.pending.pop() {
            if self.taken(node).is_some() {
                continue;
            }
            if expanded {
                self.complete(node)?;
                continue;
            }
            self.pending.push((node, true));
            self.children.clear();
            let children = &mut self.children;
            let each = |child: NodeAddress, _| {
                children.push(child);
                Ok::<(), ImageRefusal>(())
            };
            let dangling = ImageRefusal::Dangling(node);
            match node {
                NodeAddress::Producer(id) => {
                    let held = self.arena.producer(id).ok_or(dangling)?;
                    refuse_producer(held).map_err(|form| ImageRefusal::Uncodable { node, form })?;
                    producer_children(held, each)?;
                },
                NodeAddress::Consumer(id) => {
                    let held = self.arena.consumer(id).ok_or(dangling)?;
                    refuse_consumer(held).map_err(|form| ImageRefusal::Uncodable { node, form })?;
                    consumer_children(held, each)?;
                },
                NodeAddress::Command(id) => {
                    let held = self.arena.command(id).ok_or(dangling)?;
                    command_children(held, each)?;
                },
            }
            for &child in self.children.iter().rev() {
                if self.taken(child).is_none() {
                    self.pending.push((child, false));
                }
            }
        }
        self.taken(root).ok_or(ImageRefusal::Dangling(root))
    }

    /// Take `node`, whose children are taken.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// [`ImageRefusal::Dangling`] for a node the arena does not hold, and
    /// [`ImageRefusal::Mint`] for a family past its ceiling.
    ///
    /// # Cost
    /// - allocation: the node's entry and its position, growth within the
    ///   command
    fn complete(
        &mut self,
        node: NodeAddress,
    ) -> Result<(), ImageRefusal>
    {
        let dangling = ImageRefusal::Dangling(node);
        match node {
            NodeAddress::Producer(id) => {
                let held = self.arena.producer(id).ok_or(dangling)?;
                if let ProducerNode::Constant(constant) = *held
                    && self.seen.insert(constant)
                {
                    self.met.push(constant);
                }
                if let ProducerNode::Code(value) = *held {
                    self.annotate(ArenaNode::Value(value));
                }
                let at = next(
                    self.producers.len(),
                    gandr_core_sequent::NodeFamily::Producer,
                )?;
                let _fresh = self.producers.insert(id, u32::from(at));
                self.nodes.push(Node::Producer(Cow::Borrowed(held)));
            },
            NodeAddress::Consumer(id) => {
                let held = self.arena.consumer(id).ok_or(dangling)?;
                for ty in consumer_annotations(held) {
                    self.annotate(ArenaNode::ValueType(ty));
                }
                let at = next(
                    self.consumers.len(),
                    gandr_core_sequent::NodeFamily::Consumer,
                )?;
                let _fresh = self.consumers.insert(id, u32::from(at));
                self.nodes.push(Node::Consumer(
                    Cow::Borrowed(held),
                    self.arena.independence(id),
                ));
            },
            NodeAddress::Command(id) => {
                let held = self.arena.command(id).ok_or(dangling)?;
                for ty in command_annotations(held) {
                    self.annotate(ArenaNode::ValueType(ty));
                }
                let at = next(self.commands.len(), gandr_core_sequent::NodeFamily::Command)?;
                let _fresh = self.commands.insert(id, u32::from(at));
                self.nodes.push(Node::Command(Cow::Borrowed(held)));
            },
        }
        Ok(())
    }

    /// Give `node` the next ordinal of the table, on its first sight.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Cost
    /// - allocation: the root and its ordinal, growth within the annotations
    fn annotate(
        &mut self,
        node: ArenaNode,
    )
    {
        if let alloc::collections::btree_map::Entry::Vacant(entry) = self.ordinals.entry(node) {
            let _ordinal =
                entry.insert(Word32(u32::try_from(self.roots.len()).unwrap_or(u32::MAX)));
            self.roots.push(node);
        }
    }
}

/// The position after `taken` nodes of `family`.
///
/// # Specification
/// trivial.
///
/// # Errors
/// [`MintRefusal::FamilyFull`] past the arena's ceiling.
fn next<Taken>(
    taken: Taken,
    family: gandr_core_sequent::NodeFamily,
) -> Result<Word32, ImageRefusal>
where
    u32: TryFrom<Taken>,
{
    u32::try_from(taken)
        .ok()
        .filter(|&at| at < u32::MAX)
        .map(Word32)
        .ok_or(ImageRefusal::Mint(MintRefusal::FamilyFull(family)))
}

/// The form of a producer that does not cross.
///
/// # Specification
/// trivial.
///
/// # Errors
/// The form the image does not write.
const fn refuse_producer(node: &ProducerNode) -> Result<(), Uncodable>
{
    match *node {
        ProducerNode::Constructor { ref tag, .. } => refuse_head(tag),
        ProducerNode::Code(_)
        | ProducerNode::Reify(_)
        | ProducerNode::Primitive { .. }
        | ProducerNode::Decompose(_)
        | ProducerNode::Variable { .. }
        | ProducerNode::Constant(_)
        | ProducerNode::Literal(_)
        | ProducerNode::Thunk { .. }
        | ProducerNode::Fixpoint { .. }
        | ProducerNode::Cocase { .. }
        | ProducerNode::Closure { .. }
        | ProducerNode::Mu { .. } => Ok(()),
    }
}

/// The form of a consumer that does not cross.
///
/// # Specification
/// trivial.
///
/// # Errors
/// The form the image does not write.
fn refuse_consumer(node: &ConsumerNode) -> Result<(), Uncodable>
{
    match *node {
        ConsumerNode::Case { ref arms } => arms
            .iter()
            .try_for_each(|arm| refuse_head(&arm.constructor)),
        ConsumerNode::ListFold { .. }
        | ConsumerNode::Covariable(_)
        | ConsumerNode::MuTilde { .. }
        | ConsumerNode::MuTildeAll { .. }
        | ConsumerNode::Destructor { .. }
        | ConsumerNode::DataCase { .. }
        | ConsumerNode::Select { .. }
        | ConsumerNode::Top => Ok(()),
    }
}

/// A head that does not cross.
///
/// # Specification
/// trivial.
///
/// # Errors
/// [`Uncodable::Head`] for a recorded run, a dialogue or a web.
const fn refuse_head(head: &Head) -> Result<(), Uncodable>
{
    match *head {
        Head::Recorded(_) => Err(Uncodable::Head(crate::crossing::Uncrossable::Recorded)),
        Head::Dialogue(_) => Err(Uncodable::Head(crate::crossing::Uncrossable::Dialogue)),
        Head::Web(_) => Err(Uncodable::Head(crate::crossing::Uncrossable::Web)),
        Head::Tuple(_)
        | Head::Record(_)
        | Head::ListNil
        | Head::ListCons
        | Head::Injection(_)
        | Head::Lift(_)
        | Head::Data { .. } => Ok(()),
    }
}

impl<'arena> Image<'arena>
{
    /// The image of the command `root` in `arena`, with each definition that
    /// it unfolds.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success the root's nodes in completion order, then each
    ///   definition body's nodes that an earlier walk did not take, the
    ///   definitions in the order the walks met their constants.
    /// - fails: as [`encode`].
    /// - panics: none.
    /// - executable: none — as [`Walk::take`].
    ///
    /// # Errors
    /// As [`encode`].
    ///
    /// # Adequacy
    /// - hypothesis: L2 — as [`encode`].
    /// - witness: `tests::image::each_named_program_reads_back_and_runs_alike`
    ///
    /// # Cost
    /// - allocation: the walk's state and the definitions, growth within the
    ///   command
    fn of(
        arena: &'arena CommandArena,
        definitions: &Definitions,
        root: CommandId,
    ) -> Result<Self, ImageRefusal>
    {
        let mut walk = Walk {
            arena,
            nodes: Vec::new(),
            producers: BTreeMap::new(),
            consumers: BTreeMap::new(),
            commands: BTreeMap::new(),
            met: Vec::new(),
            seen: BTreeSet::new(),
            pending: Vec::new(),
            children: Vec::new(),
            roots: Vec::new(),
            ordinals: BTreeMap::new(),
        };
        let root = CommandId::from(walk.take(NodeAddress::Command(root))?);
        let mut written = Vec::new();
        let mut at = 0_usize;
        while let Some(&constant) = walk.met.get(at) {
            at = at.saturating_add(1_usize);
            let definition = match definitions.get(constant) {
                None => return Err(ImageRefusal::Undefined(constant)),
                Some(Definition::Opaque) => Definition::Opaque,
                Some(Definition::Transparent(body)) => Definition::Transparent(ProducerId::from(
                    walk.take(NodeAddress::Producer(body))?,
                )),
            };
            written.push((constant, definition));
        }
        let counts = [
            u32::from(next(
                walk.producers.len(),
                gandr_core_sequent::NodeFamily::Producer,
            )?),
            u32::from(next(
                walk.consumers.len(),
                gandr_core_sequent::NodeFamily::Consumer,
            )?),
            u32::from(next(
                walk.commands.len(),
                gandr_core_sequent::NodeFamily::Command,
            )?),
        ];
        let annotations = if walk.roots.is_empty() {
            Annotations::default()
        }
        else {
            let (table, ordinals) = annotations::Table::of(arena.annotations(), &walk.roots);
            Annotations {
                roots: usize::from(table.roots()),
                bytes: table.bytes().map_err(ImageRefusal::Table)?,
                ordinals: walk.roots.iter().copied().zip(ordinals).collect(),
            }
        };
        Ok(Self {
            nodes: walk.nodes,
            numbering: Numbering::Taken {
                producers: walk.producers,
                consumers: walk.consumers,
                commands: walk.commands,
            },
            counts,
            definitions: written,
            root,
            annotations,
        })
    }

    /// Mint the nodes into a fresh arena in order, then check the root.
    ///
    /// # Specification
    /// - requires: the image was read, so each id is its position.
    /// - ensures: as [`read`].
    /// - fails: as [`read`].
    /// - panics: none.
    /// - executable: none — as [`read`].
    ///
    /// # Errors
    /// As [`read`].
    ///
    /// # Adequacy
    /// - hypothesis: L2 — as [`read`].
    /// - witness: `tests::image::each_named_program_reads_back_and_runs_alike`
    /// - witness: `tests::image::each_fault_of_the_bytes_is_refused_by_name`
    ///
    /// # Cost
    /// - allocation: the fresh arena and the definitions, durable by the read
    ///   command
    fn mint(self) -> Result<Read, ImageRefusal>
    {
        let mut arena = CommandArena::new();
        let roots = if self.annotations.roots == 0 {
            Vec::new()
        }
        else {
            let table =
                annotations::Table::read(&self.annotations.bytes, Ordinal(self.annotations.roots))
                    .map_err(ImageRefusal::Table)?;
            match table.mint(arena.annotations_mut()) {
                Maybe::Present(roots) => roots,
                Maybe::Absent(reason) => return Err(ImageRefusal::Annotation(reason)),
            }
        };
        for node in self.nodes {
            match node {
                Node::Producer(node) => {
                    let _id = arena.mint_producer(node.into_owned())?;
                },
                Node::Consumer(node, independence) => {
                    let id = arena.mint_consumer(node.into_owned())?;
                    if independence == Independence::Independent {
                        arena.mark_independent(id).map_err(ImageRefusal::Mark)?;
                    }
                },
                Node::Command(node) => {
                    let _id = arena.mint_command(node.into_owned())?;
                },
                Node::Pending(pending) => match settle(pending, &roots)? {
                    Settled::Producer(node) => {
                        let _id = arena.mint_producer(node)?;
                    },
                    Settled::Consumer(node) => {
                        let _id = arena.mint_consumer(node)?;
                    },
                    Settled::Command(node) => {
                        let _id = arena.mint_command(node)?;
                    },
                },
            }
        }
        let mut entries: BTreeMap<ConstantIndex, Definition> = BTreeMap::new();
        for (constant, definition) in self.definitions {
            if let Definition::Transparent(body) = definition
                && arena.producer(body).is_none()
            {
                return Err(ImageRefusal::Mint(MintRefusal::DanglingProducer(body)));
            }
            if entries.insert(constant, definition).is_some() {
                return Err(ImageRefusal::Defined(constant));
            }
        }
        let mut definitions = Definitions::new();
        for (&constant, &definition) in &entries {
            while usize::from(definitions.len()) < usize::from(constant) {
                let _opaque = definitions.push(Definition::Opaque);
            }
            let _at = definitions.push(definition);
        }
        let free = check_command(&arena, self.root).map_err(ImageRefusal::Check)?;
        if free != FreeSet::default() {
            return Err(ImageRefusal::Open(free));
        }
        Ok(Read {
            arena,
            definitions,
            root: self.root,
        })
    }
}

/// A pending node with each annotation minted: a node of one family.
///
/// # Specification
/// trivial.
enum Settled
{
    /// A producer.
    Producer(ProducerNode),
    /// A consumer.
    Consumer(ConsumerNode),
    /// A command.
    Command(CommandNode),
}

/// The node of `pending`, each ordinal read as the root that `roots` minted
/// for it.
///
/// # Specification
/// - requires: nothing.
/// - ensures: on success the node of the IL that `pending` writes, over the
///   minted roots.
/// - fails: an ordinal past the roots, a root of another sort, and bytes of a
///   signature or an action that the node codec refuses.
/// - panics: none.
/// - executable: none — the check of the read root is the postcondition, and it
///   runs.
///
/// # Errors
/// [`ImageRefusal::Annotation`] and [`ImageRefusal::Table`].
///
/// # Adequacy
/// - hypothesis: L2 — a code reads back to a command that checks. L3 — a root
///   past its table is refused by name.
/// - witness: `tests::image::a_code_round_trips_and_a_fault_of_its_table_is_refused_by_name`
///
/// # Cost
/// - allocation: the signature or the action of the node, durable by the read
///   command
fn settle(
    pending: Pending,
    roots: &[ArenaNode],
) -> Result<Settled, ImageRefusal>
{
    Ok(match pending {
        Pending::Code(ordinal) => match root(roots, ordinal)? {
            ArenaNode::Value(id) => Settled::Producer(ProducerNode::Code(id)),
            ArenaNode::ValueType(_) | ArenaNode::Computation(_) | ArenaNode::CompType(_) => {
                return Err(ImageRefusal::Annotation(seating::Absent::IllSorted));
            },
        },
        Pending::ListFold {
            element,
            result,
            on_nil,
            on_cons,
            continuation,
        } => Settled::Consumer(ConsumerNode::ListFold {
            element: value_type(roots, element)?,
            result: value_type(roots, result)?,
            on_nil,
            on_cons,
            continuation,
        }),
        Pending::Perform {
            signature,
            operation,
            route,
            payload,
            continuation,
        } => Settled::Command(CommandNode::Perform {
            signature: signature_of(&signature, roots)?,
            operation,
            route,
            payload,
            continuation,
        }),
        Pending::Handle {
            signature,
            introduces,
            subject,
            on_return,
            clauses,
            continuation,
        } => Settled::Command(CommandNode::Handle {
            signature: signature_of(&signature, roots)?,
            introduces,
            subject,
            on_return,
            clauses,
            continuation,
        }),
        Pending::Session {
            action,
            continuation,
        } => Settled::Command(CommandNode::Session {
            action: action_of(&action, roots)?,
            continuation,
        }),
    })
}

/// The root at `ordinal`.
///
/// # Specification
/// trivial.
///
/// # Errors
/// [`ImageRefusal::Annotation`] for an ordinal past the roots.
fn root(
    roots: &[ArenaNode],
    ordinal: Word32,
) -> Result<ArenaNode, ImageRefusal>
{
    usize::try_from(u32::from(ordinal))
        .ok()
        .and_then(|at| roots.get(at))
        .copied()
        .ok_or(ImageRefusal::Annotation(seating::Absent::Unplaced))
}

/// The value type at `ordinal`.
///
/// # Specification
/// trivial.
///
/// # Errors
/// [`ImageRefusal::Annotation`] for an ordinal past the roots or a root of
/// another sort.
fn value_type(
    roots: &[ArenaNode],
    ordinal: Word32,
) -> Result<ValueTypeId, ImageRefusal>
{
    match root(roots, ordinal)? {
        ArenaNode::ValueType(id) => Ok(id),
        ArenaNode::Value(_) | ArenaNode::Computation(_) | ArenaNode::CompType(_) => {
            Err(ImageRefusal::Annotation(seating::Absent::IllSorted))
        },
    }
}

/// The value type at the ordinal `index`.
///
/// # Specification
/// trivial.
///
/// # Errors
/// As [`value_type`].
fn indexed_type(
    roots: &[ArenaNode],
    index: NodeIndex,
) -> Result<ValueTypeId, ImageRefusal>
{
    value_type(
        roots,
        Word32(u32::try_from(usize::from(index)).unwrap_or(u32::MAX)),
    )
}

/// The position that the node index `index` writes.
///
/// # Specification
/// trivial.
///
/// # Errors
/// [`ImageRefusal::Table`] for an index past 32 bits.
fn indexed_position(index: NodeIndex) -> Result<Word32, ImageRefusal>
{
    u32::try_from(usize::from(index))
        .map(Word32)
        .map_err(|_wider| ImageRefusal::Table(CodecError::Corrupt))
}

/// The interface that `bytes` write over ordinals, over the minted roots.
///
/// # Specification
/// trivial.
///
/// # Errors
/// [`ImageRefusal::Table`] for bytes that the node codec refuses, and as
/// [`value_type`].
///
/// # Cost
/// - allocation: the operations of the interface, durable by the read command
fn signature_of(
    bytes: &annotations::Buffer,
    roots: &[ArenaNode],
) -> Result<EffectSig, ImageRefusal>
{
    let mut reader = NodeReader {
        bytes: bytes.as_ref(),
        cursor: 0,
    };
    let indexed = read_effect_signature(&mut reader).map_err(ImageRefusal::Table)?;
    reader.finish().map_err(ImageRefusal::Table)?;
    let mut operations = Vec::with_capacity(indexed.operations().len());
    for operation in indexed.operations() {
        operations.push(EffectOp {
            name: operation.name.clone(),
            payload: indexed_type(roots, operation.payload)?,
            reply: indexed_type(roots, operation.reply)?,
        });
    }
    EffectSig::new(indexed.name().clone(), operations)
        .map_err(|_conflict| ImageRefusal::Table(CodecError::NonCanonical))
}

/// The session action that `bytes` write over positions and ordinals.
///
/// # Specification
/// trivial.
///
/// # Errors
/// [`ImageRefusal::Table`] for bytes that the node codec refuses, and as
/// [`value_type`].
///
/// # Cost
/// - allocation: the label and the arms of the action, durable by the read
///   command
fn action_of(
    bytes: &annotations::Buffer,
    roots: &[ArenaNode],
) -> Result<SessionAction<ProducerId, CommandId, ValueTypeId>, ImageRefusal>
{
    let mut reader = NodeReader {
        bytes: bytes.as_ref(),
        cursor: 0,
    };
    let indexed = read_session_action(&mut reader).map_err(ImageRefusal::Table)?;
    reader.finish().map_err(ImageRefusal::Table)?;
    indexed.try_map(
        ChildOrder::Forward,
        &mut (),
        |_state: &mut (), value| indexed_position(value).map(ProducerId::from),
        |_state: &mut (), body| indexed_position(body).map(CommandId::from),
        |_state: &mut (), ty| indexed_type(roots, ty),
    )
}

impl CanonicalValue for Image<'_>
{
    /// Write the image's open and counts, each node, each definition, and
    /// the close.
    ///
    /// # Specification
    /// - requires: the image's numbering takes each child that a node names.
    /// - ensures: on success one balanced value, as the module's table states.
    /// - fails: the sink's refusal.
    /// - panics: none.
    /// - executable: none — the walk is its own specification.
    ///
    /// # Errors
    /// The first [`ValueError`] the sink returns.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — as [`encode`].
    /// - witness: `tests::image::each_named_program_reads_back_and_runs_alike`
    fn emit_tokens<Sink>(
        &self,
        sink: &mut Sink,
    ) -> Result<(), ValueError>
    where
        Sink: TokenSink + ?Sized,
    {
        let annotated = self.annotations.roots != 0;
        sink.open(ConstructorTag::from(if annotated {
            ANNOTATED
        }
        else {
            IMAGE
        }))?;
        for &family in &self.counts {
            sink.word(position(family))?;
        }
        sink.word(count(self.definitions.len())?)?;
        sink.word(position(u32::from(self.root)))?;
        if annotated {
            sink.word(count(self.annotations.roots)?)?;
            sink.bytes(TokenBytes::from(self.annotations.bytes.as_ref()))?;
        }
        for node in &self.nodes {
            match *node {
                Node::Producer(ref node) => self.emit_producer(node, sink)?,
                Node::Consumer(ref node, independence) => {
                    self.emit_consumer(node, independence, sink)?;
                },
                Node::Command(ref node) => self.emit_command(node, sink)?,
                Node::Pending(_) => return Err(untaken()),
            }
        }
        for &(constant, definition) in &self.definitions {
            sink.open(ConstructorTag::from(DEFINITION))?;
            sink.word(count(usize::from(constant))?)?;
            sink.word(match definition {
                Definition::Opaque => CanonicalWord::from(0_u64),
                Definition::Transparent(body) => {
                    CanonicalWord::from(u64::from(u32::from(body)).saturating_add(1_u64))
                },
            })?;
            sink.close()?;
        }
        sink.close()
    }

    /// Read the image's counts, then as many nodes and definitions as they
    /// state.
    ///
    /// # Specification
    /// - requires: `reader` stands at the image's open.
    /// - ensures: on success the nodes in order, each child named by its
    ///   position, the reader past the image's close.
    /// - fails: the reader's refusal; a count past [`MOST`] before any node is
    ///   read; a tag that no node has or a payload its form does not write, as
    ///   that node's constructor at its open record; and the image's
    ///   constructor when a family's nodes differ from its count.
    /// - panics: none.
    /// - executable: none — the walk is its own specification.
    ///
    /// # Errors
    /// [`ValueError`]: as listed above.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — as [`read`]; L3 — as [`read`].
    /// - witness: `tests::image::each_named_program_reads_back_and_runs_alike`
    /// - witness: `tests::image::each_fault_of_the_bytes_is_refused_by_name`
    ///
    /// # Cost
    /// - allocation: the nodes and the definitions, growth within the image
    fn decode_tokens<Store>(reader: &mut TokenReader<'_, Store>) -> Result<Self, ValueError>
    where
        Store: ChunkStore,
    {
        let opened = Opened::open(reader)?;
        let annotated = match u8::from(opened.tag()) {
            IMAGE => false,
            ANNOTATED => true,
            _ => return Err(opened.refused()),
        };
        let mut stated = [0_u32; 3];
        for family in &mut stated {
            *family = u32::from(bounded(reader)?);
        }
        let definitions = u32::from(bounded(reader)?);
        let root = CommandId::from(index(opened, reader)?);
        let annotations = if annotated {
            let roots = usize::try_from(u32::from(bounded(reader)?))
                .ok()
                .filter(|&roots| roots != 0)
                .ok_or_else(|| opened.refused())?;
            Annotations {
                roots,
                bytes: annotations::Buffer::from(<&[u8]>::from(reader.read_bytes()?).to_vec()),
                ordinals: BTreeMap::new(),
            }
        }
        else {
            Annotations::default()
        };
        let nodes = stated.iter().map(|&family| u64::from(family)).sum::<u64>();
        if nodes > MOST {
            return Err(ValueError::DecodeBudgetExceeded {
                spent: DecodeWork::from(nodes),
                ceiling: DecodeWork::from(MOST),
            });
        }
        let mut read = Vec::new();
        let mut counts = [0_u32; 3];
        for _node in 0_u64 .. nodes {
            let node = read_node(reader)?;
            let family = match node {
                Node::Producer(_) | Node::Pending(Pending::Code(_)) => counts.get_mut(0_usize),
                Node::Consumer(..) | Node::Pending(Pending::ListFold { .. }) => {
                    counts.get_mut(1_usize)
                },
                Node::Command(_)
                | Node::Pending(
                    Pending::Perform { .. } | Pending::Handle { .. } | Pending::Session { .. },
                ) => counts.get_mut(2_usize),
            };
            if let Some(family) = family {
                *family = family.saturating_add(1_u32);
            }
            read.push(node);
        }
        if counts != stated {
            return Err(opened.refused());
        }
        let mut written = Vec::new();
        for _definition in 0_u32 .. definitions {
            let row = Opened::open(reader)?;
            if u8::from(row.tag()) != DEFINITION {
                return Err(row.refused());
            }
            let constant = ConstantIndex::from(
                usize::try_from(u32::from(bounded(reader)?)).map_err(|_wider| row.refused())?,
            );
            let definition = match u64::from(reader.read_word()?) {
                0_u64 => Definition::Opaque,
                past => {
                    let body = u32::try_from(past.saturating_sub(1_u64))
                        .map_err(|_wider| row.refused())?;
                    Definition::Transparent(ProducerId::from(body))
                },
            };
            reader.read_close()?;
            written.push((constant, definition));
        }
        reader.read_close()?;
        Ok(Self {
            nodes: read,
            numbering: Numbering::Read,
            counts,
            definitions: written,
            root,
            annotations,
        })
    }
}

/// Read a count that [`MOST`] bounds.
///
/// # Specification
/// trivial.
///
/// # Errors
/// The reader's refusal, and [`ValueError::DecodeBudgetExceeded`] for a
/// count past [`MOST`].
///
/// # Cost
/// - allocation: a suspended frame of the reader, growth within the decode
///   budget
fn bounded<Store>(reader: &mut TokenReader<'_, Store>) -> Result<Word32, ValueError>
where
    Store: ChunkStore,
{
    let stated = u64::from(reader.read_word()?);
    let past = ValueError::DecodeBudgetExceeded {
        spent: DecodeWork::from(stated),
        ceiling: DecodeWork::from(MOST),
    };
    if stated > MOST {
        return Err(past);
    }
    u32::try_from(stated).map(Word32).map_err(|_wider| past)
}

/// Read a position or an index that a node holds in 32 bits.
///
/// # Specification
/// trivial.
///
/// # Errors
/// The reader's refusal, and `opened`'s for a word wider than 32 bits.
///
/// # Cost
/// - allocation: a suspended frame of the reader, growth within the decode
///   budget
fn index<Store>(
    opened: Opened,
    reader: &mut TokenReader<'_, Store>,
) -> Result<Word32, ValueError>
where
    Store: ChunkStore,
{
    u32::try_from(u64::from(reader.read_word()?))
        .map(Word32)
        .map_err(|_wider| opened.refused())
}

/// Read a count, an ordinal or a constant that the host's counts hold.
///
/// # Specification
/// trivial.
///
/// # Errors
/// The reader's refusal, and `opened`'s for a word wider than the host's
/// counts.
///
/// # Cost
/// - allocation: a suspended frame of the reader, growth within the decode
///   budget
fn ordinal<Store>(
    opened: Opened,
    reader: &mut TokenReader<'_, Store>,
) -> Result<Ordinal, ValueError>
where
    Store: ChunkStore,
{
    usize::try_from(u64::from(reader.read_word()?))
        .map(Ordinal)
        .map_err(|_wider| opened.refused())
}

/// Read a word that names one of `choices` cases, from zero.
///
/// # Specification
/// trivial.
///
/// # Errors
/// The reader's refusal, and `opened`'s for a case past the last.
///
/// # Cost
/// - allocation: a suspended frame of the reader, growth within the decode
///   budget
fn case<Store, Read>(
    opened: Opened,
    reader: &mut TokenReader<'_, Store>,
    choices: impl Into<Choices>,
) -> Result<Read, ValueError>
where
    Store: ChunkStore,
    Read: From<Case>,
{
    let read = u64::from(reader.read_word()?);
    if read < choices.into().0 {
        Ok(Read::from(Case(read)))
    }
    else {
        Err(opened.refused())
    }
}

impl From<u64> for Choices
{
    /// The count of cases.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(choices: u64) -> Self
    {
        Self(choices)
    }
}

impl From<Case> for u64
{
    /// The case's number, from zero.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(case: Case) -> Self
    {
        case.0
    }
}

impl From<Ordinal> for usize
{
    /// The ordinal's count.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(ordinal: Ordinal) -> Self
    {
        ordinal.0
    }
}

impl From<Word32> for u32
{
    /// The position.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(word: Word32) -> Self
    {
        word.0
    }
}

/// Read a list of `u32` positions after its count.
///
/// # Specification
/// trivial.
///
/// # Errors
/// As [`index`], and the reader's refusal of a list longer than the stream.
///
/// # Cost
/// - allocation: the list, durable by its node
fn positions<Store, Id>(
    opened: Opened,
    reader: &mut TokenReader<'_, Store>,
) -> Result<Box<[Id]>, ValueError>
where
    Store: ChunkStore,
    Id: From<Word32>,
{
    let length = usize::from(ordinal(opened, reader)?);
    let mut read = Vec::new();
    for _at in 0_usize .. length {
        read.push(Id::from(index(opened, reader)?));
    }
    Ok(read.into_boxed_slice())
}

/// Read a destructor head.
///
/// # Specification
/// trivial.
///
/// # Errors
/// As [`case`] and [`ordinal`].
fn destructor<Store>(
    opened: Opened,
    reader: &mut TokenReader<'_, Store>,
) -> Result<DestructorTag, ValueError>
where
    Store: ChunkStore,
{
    Ok(match case(opened, reader, 3_u64)? {
        0_u64 => DestructorTag::Apply,
        1_u64 => DestructorTag::Force,
        _ => DestructorTag::Project(Component::from(ordinal(opened, reader)?)),
    })
}

/// Read one node: its open, its payload and its close.
///
/// # Specification
/// - requires: the reader stands at a node's open.
/// - ensures: on success the node its tag and its payload name, each child id
///   the position that the bytes state.
/// - fails: the reader's refusal, and the node's constructor at its open for a
///   tag that no node has or a payload that its form does not write.
/// - panics: none.
/// - executable: none — the tag table is its own specification.
///
/// # Errors
/// [`ValueError`]: as listed above.
///
/// # Adequacy
/// - hypothesis: L2 — as [`read`]; L3 — a tag that no node has is refused at
///   its open.
/// - witness: `tests::image::each_named_program_reads_back_and_runs_alike`
/// - witness: `tests::image::each_fault_of_the_bytes_is_refused_by_name`
///
/// # Cost
/// - allocation: the node's lists and payloads, durable by the node
#[expect(
    clippy::too_many_lines,
    reason = "one arm for each node form of the IL, in the order the IL declares them"
)]
fn read_node<Store>(reader: &mut TokenReader<'_, Store>) -> Result<Node<'static>, ValueError>
where
    Store: ChunkStore,
{
    let opened = Opened::open(reader)?;
    let producer = |node: ProducerNode| Node::Producer(Cow::Owned(node));
    let consumer = |node: ConsumerNode| Node::Consumer(Cow::Owned(node), Independence::Sequential);
    let command = |node: CommandNode| Node::Command(Cow::Owned(node));
    let node = match u8::from(opened.tag()) {
        REIFY => {
            let length = usize::from(ordinal(opened, reader)?);
            let mut frames = Vec::new();
            for _frame in 0_usize .. length {
                frames.push(match case(opened, reader, 3_u64)? {
                    0_u64 => StackFrame::Apply(ProducerId::from(index(opened, reader)?)),
                    1_u64 => StackFrame::Bind(CommandId::from(index(opened, reader)?)),
                    _ => StackFrame::Project(Component::from(ordinal(opened, reader)?)),
                });
            }
            producer(ProducerNode::Reify(Arc::from(frames)))
        },
        PRIMITIVE => {
            let primitive = PRELUDE
                .get(usize::from(ordinal(opened, reader)?))
                .copied()
                .ok_or_else(|| opened.refused())?;
            let arguments = match case(opened, reader, 3_u64)? {
                1_u64 => Arguments::Unary(ProducerId::from(index(opened, reader)?)),
                2_u64 => {
                    let first = ProducerId::from(index(opened, reader)?);
                    Arguments::Binary([first, ProducerId::from(index(opened, reader)?)])
                },
                _ => return Err(opened.refused()),
            };
            producer(ProducerNode::Primitive {
                primitive,
                arguments,
            })
        },
        DECOMPOSE => producer(ProducerNode::Decompose(ProducerId::from(index(
            opened, reader,
        )?))),
        VARIABLE => {
            let zone = match case(opened, reader, 2_u64)? {
                0_u64 => Zone::Intuitionistic,
                _ => Zone::Linear,
            };
            producer(ProducerNode::Variable {
                zone,
                index: DeBruijnIndex::from(index(opened, reader)?),
            })
        },
        CONSTANT => producer(ProducerNode::Constant(ConstantIndex::from(ordinal(
            opened, reader,
        )?))),
        LITERAL => {
            let literal = read_literal(reader)?;
            reader.read_close()?;
            producer(ProducerNode::Literal(literal))
        },
        CONSTRUCTOR => {
            let tag = read_head(reader)?;
            reader.read_close()?;
            let producers = positions(opened, reader)?;
            let consumers = positions(opened, reader)?;
            producer(ProducerNode::Constructor {
                tag,
                producers,
                consumers,
            })
        },
        THUNK => producer(ProducerNode::Thunk {
            body: CommandId::from(index(opened, reader)?),
        }),
        FIXPOINT => {
            let body = CommandId::from(index(opened, reader)?);
            let evidence = match case(opened, reader, 5_u64)? {
                0_u64 => FixpointEvidence::Partial,
                1_u64 => FixpointEvidence::StructuralDescent,
                2_u64 => FixpointEvidence::Staged {
                    position: StagedPosition::from(ordinal(opened, reader)?),
                },
                3_u64 => {
                    let length = usize::from(ordinal(opened, reader)?);
                    let mut read = Vec::new();
                    for _component in
                        0_usize .. length.min(JointPositions::CAPACITY.saturating_add(1_usize))
                    {
                        read.push(StagedPosition::from(ordinal(opened, reader)?));
                    }
                    FixpointEvidence::Joint {
                        positions: JointPositions::new(&read).ok_or_else(|| opened.refused())?,
                    }
                },
                _ => FixpointEvidence::Guarded,
            };
            producer(ProducerNode::Fixpoint { body, evidence })
        },
        COCASE => {
            let length = usize::from(ordinal(opened, reader)?);
            let mut arms = Vec::new();
            for _arm in 0_usize .. length {
                let head = destructor(opened, reader)?;
                arms.push(CopatternArm {
                    destructor: head,
                    body: CommandId::from(index(opened, reader)?),
                });
            }
            producer(ProducerNode::Cocase {
                arms: arms.into_boxed_slice(),
            })
        },
        CLOSURE => {
            let environment = positions(opened, reader)?;
            producer(ProducerNode::Closure {
                environment,
                code: ProducerId::from(index(opened, reader)?),
            })
        },
        MU => producer(ProducerNode::Mu {
            body: CommandId::from(index(opened, reader)?),
        }),
        COVARIABLE => consumer(ConsumerNode::Covariable(CovariableIndex::from(index(
            opened, reader,
        )?))),
        MU_TILDE => {
            let independence = match case(opened, reader, 2_u64)? {
                0_u64 => Independence::Sequential,
                _ => Independence::Independent,
            };
            let body = CommandId::from(index(opened, reader)?);
            Node::Consumer(Cow::Owned(ConsumerNode::MuTilde { body }), independence)
        },
        MU_TILDE_ALL => {
            let arity = ProducerArity::from(ordinal(opened, reader)?);
            consumer(ConsumerNode::MuTildeAll {
                arity,
                body: CommandId::from(index(opened, reader)?),
            })
        },
        DESTRUCTOR => {
            let tag = destructor(opened, reader)?;
            let producers = positions(opened, reader)?;
            let consumers = positions(opened, reader)?;
            consumer(ConsumerNode::Destructor {
                tag,
                producers,
                consumers,
            })
        },
        CASE => {
            let length = usize::from(ordinal(opened, reader)?);
            let mut arms = Vec::new();
            for _arm in 0_usize .. length {
                let constructor = read_head(reader)?;
                reader.read_close()?;
                arms.push(PatternArm {
                    constructor,
                    body: CommandId::from(index(opened, reader)?),
                });
            }
            consumer(ConsumerNode::Case {
                arms: arms.into_boxed_slice(),
            })
        },
        DATA_CASE => {
            let branches = positions(opened, reader)?;
            let length = usize::from(ordinal(opened, reader)?);
            let mut arities = Vec::new();
            for _arity in 0_usize .. length {
                arities.push(FieldCount::from(ordinal(opened, reader)?));
            }
            consumer(ConsumerNode::DataCase {
                branches,
                arities: arities.into_boxed_slice(),
                then: ConsumerId::from(index(opened, reader)?),
            })
        },
        SELECT => {
            let selector = match case(opened, reader, 2_u64)? {
                0_u64 => Selector::Component(Component::from(ordinal(opened, reader)?)),
                _ => Selector::Label(FieldLabel::from(opened.text(reader)?)),
            };
            consumer(ConsumerNode::Select {
                selector,
                then: ConsumerId::from(index(opened, reader)?),
            })
        },
        TOP => consumer(ConsumerNode::Top),
        RESUME => {
            let stack = ProducerId::from(index(opened, reader)?);
            let body = CommandId::from(index(opened, reader)?);
            command(CommandNode::Resume {
                stack,
                body,
                continuation: ConsumerId::from(index(opened, reader)?),
            })
        },
        ABANDON => {
            let stack = ProducerId::from(index(opened, reader)?);
            command(CommandNode::Abandon {
                stack,
                continuation: ConsumerId::from(index(opened, reader)?),
            })
        },
        RESET | SHIFT => {
            let body = CommandId::from(index(opened, reader)?);
            let continuation = ConsumerId::from(index(opened, reader)?);
            command(if u8::from(opened.tag()) == RESET {
                CommandNode::Reset { body, continuation }
            }
            else {
                CommandNode::Shift { body, continuation }
            })
        },
        CUT => {
            let polarity = match case(opened, reader, 2_u64)? {
                0_u64 => Polarity::Positive,
                _ => Polarity::Negative,
            };
            let producer = ProducerId::from(index(opened, reader)?);
            command(CommandNode::Cut {
                polarity,
                producer,
                consumer: ConsumerId::from(index(opened, reader)?),
            })
        },
        DELIVER => {
            let producers = positions(opened, reader)?;
            command(CommandNode::Deliver {
                producers,
                consumer: ConsumerId::from(index(opened, reader)?),
            })
        },
        MEMORY => {
            let form = read_memory(opened, reader)?;
            command(CommandNode::Memory {
                form,
                continuation: ConsumerId::from(index(opened, reader)?),
            })
        },
        WORLD => {
            let form = match case(opened, reader, 3_u64)? {
                0_u64 => WorldForm::Hold {
                    value: ProducerId::from(index(opened, reader)?),
                },
                1_u64 => {
                    let world = read_world(opened, reader)?;
                    let value = ProducerId::from(index(opened, reader)?);
                    WorldForm::Leta {
                        world,
                        value,
                        body: CommandId::from(index(opened, reader)?),
                    }
                },
                _ => {
                    let world = read_world(opened, reader)?;
                    WorldForm::Migrate {
                        world,
                        body: CommandId::from(index(opened, reader)?),
                    }
                },
            };
            command(CommandNode::World {
                form,
                continuation: ConsumerId::from(index(opened, reader)?),
            })
        },
        CODE => Node::Pending(Pending::Code(index(opened, reader)?)),
        LIST_FOLD => {
            let element = index(opened, reader)?;
            let result = index(opened, reader)?;
            let on_nil = CommandId::from(index(opened, reader)?);
            let on_cons = CommandId::from(index(opened, reader)?);
            Node::Pending(Pending::ListFold {
                element,
                result,
                on_nil,
                on_cons,
                continuation: ConsumerId::from(index(opened, reader)?),
            })
        },
        PERFORM => {
            let signature = annotations::Buffer::from(<&[u8]>::from(reader.read_bytes()?).to_vec());
            let operation = OperationName::from(opened.text(reader)?.as_str());
            let route = match case(opened, reader, 2_u64)? {
                0_u64 => Route::Nearest,
                _ => Route::Capability(ProducerId::from(index(opened, reader)?)),
            };
            let payload = ProducerId::from(index(opened, reader)?);
            Node::Pending(Pending::Perform {
                signature,
                operation,
                route,
                payload,
                continuation: ConsumerId::from(index(opened, reader)?),
            })
        },
        HANDLE => {
            let signature = annotations::Buffer::from(<&[u8]>::from(reader.read_bytes()?).to_vec());
            let introduces = match case(opened, reader, 2_u64)? {
                0_u64 => Introduces::Nothing,
                _ => Introduces::Capability,
            };
            let subject = CommandId::from(index(opened, reader)?);
            let on_return = CommandId::from(index(opened, reader)?);
            let length = usize::from(ordinal(opened, reader)?);
            let mut clauses = Vec::new();
            for _clause in 0_usize .. length {
                let operation = OperationName::from(opened.text(reader)?.as_str());
                clauses.push(EffectClause {
                    operation,
                    body: CommandId::from(index(opened, reader)?),
                });
            }
            Node::Pending(Pending::Handle {
                signature,
                introduces,
                subject,
                on_return,
                clauses: Arc::from(clauses),
                continuation: ConsumerId::from(index(opened, reader)?),
            })
        },
        SESSION => {
            let action = annotations::Buffer::from(<&[u8]>::from(reader.read_bytes()?).to_vec());
            Node::Pending(Pending::Session {
                action,
                continuation: ConsumerId::from(index(opened, reader)?),
            })
        },
        _ => return Err(opened.refused()),
    };
    reader.read_close()?;
    Ok(node)
}

/// Read a memory form's case and operands.
///
/// # Specification
/// trivial.
///
/// # Errors
/// As [`case`] and [`index`].
fn read_memory<Store>(
    opened: Opened,
    reader: &mut TokenReader<'_, Store>,
) -> Result<MemoryForm<ProducerId, CommandId>, ValueError>
where
    Store: ChunkStore,
{
    Ok(match case(opened, reader, 5_u64)? {
        0_u64 => {
            let value = ProducerId::from(index(opened, reader)?);
            let body = CommandId::from(index(opened, reader)?);
            let grade = match case(opened, reader, 2_u64)? {
                0_u64 => HoldGrade::Many,
                _ => HoldGrade::One,
            };
            MemoryForm::Hold { value, body, grade }
        },
        1_u64 => {
            let mode = match case(opened, reader, 2_u64)? {
                0_u64 => AccessMode::Shared,
                _ => AccessMode::Exclusive {
                    unwind: CommandId::from(index(opened, reader)?),
                },
            };
            let held = DeBruijnIndex::from(index(opened, reader)?);
            let place = match case(opened, reader, 2_u64)? {
                0_u64 => Place::Whole,
                _ => Place::At {
                    index: ProducerId::from(index(opened, reader)?),
                },
            };
            MemoryForm::Access {
                mode,
                held,
                place,
                body: CommandId::from(index(opened, reader)?),
            }
        },
        2_u64 => {
            let view = DeBruijnIndex::from(index(opened, reader)?);
            MemoryForm::Resume {
                view,
                value: ProducerId::from(index(opened, reader)?),
            }
        },
        3_u64 => MemoryForm::Abort {
            view: DeBruijnIndex::from(index(opened, reader)?),
        },
        _ => MemoryForm::Consume {
            held: DeBruijnIndex::from(index(opened, reader)?),
        },
    })
}

/// Read a world: zero for the host's, or one and the declaration's position.
///
/// # Specification
/// trivial.
///
/// # Errors
/// As [`case`] and [`ordinal`].
fn read_world<Store>(
    opened: Opened,
    reader: &mut TokenReader<'_, Store>,
) -> Result<World, ValueError>
where
    Store: ChunkStore,
{
    Ok(match case(opened, reader, 2_u64)? {
        0_u64 => World::Host,
        _ => World::Declared(ConstantIndex::from(ordinal(opened, reader)?)),
    })
}

impl Image<'_>
{
    /// The ordinal of the root `node` in the table.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// [`untaken`] for a root that the walk did not meet.
    fn ordinal(
        &self,
        node: ArenaNode,
    ) -> Result<Word32, ValueError>
    {
        self.annotations
            .ordinals
            .get(&node)
            .copied()
            .ok_or_else(untaken)
    }

    /// The ordinal of the root `ty`, as a node index of the node codec.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// As [`Self::ordinal`].
    fn indexed(
        &self,
        ty: ValueTypeId,
    ) -> Result<NodeIndex, ValueError>
    {
        let ordinal = self.ordinal(ArenaNode::ValueType(ty))?;
        usize::try_from(u32::from(ordinal))
            .map(NodeIndex::from)
            .map_err(|_wider| untaken())
    }

    /// The bytes of the interface `signature`, each type as its ordinal, in
    /// the node codec of `gandr-core-content`.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// As [`Self::ordinal`], and [`untaken`] for a signature that the node
    /// codec does not write.
    ///
    /// # Cost
    /// - allocation: the operations and the bytes of the interface, growth
    ///   within the image
    fn signature_bytes(
        &self,
        signature: &EffectSig,
    ) -> Result<annotations::Buffer, ValueError>
    {
        let mut operations = Vec::with_capacity(signature.operations().len());
        for operation in signature.operations() {
            operations.push(EffectOp {
                name: operation.name.clone(),
                payload: self.indexed(operation.payload)?,
                reply: self.indexed(operation.reply)?,
            });
        }
        let indexed =
            EffectSig::new(signature.name().clone(), operations).map_err(|_conflict| untaken())?;
        let mut buffer = annotations::Buffer::default();
        write_effect_signature(&mut NodeWriter { sink: &mut buffer }, &indexed)
            .map_err(|_unwritten| untaken())?;
        Ok(buffer)
    }

    /// The bytes of the session action `action`, each child as its position
    /// and each type as its ordinal, in the node codec of `gandr-core-content`.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// As [`Self::ordinal`], and [`untaken`] for an action that the node codec
    /// does not write.
    ///
    /// # Cost
    /// - allocation: the label, the arms and the bytes of the action, growth
    ///   within the image
    fn action_bytes(
        &self,
        action: &SessionAction<ProducerId, CommandId, ValueTypeId>,
    ) -> Result<annotations::Buffer, ValueError>
    {
        let at = |word: CanonicalWord| {
            usize::try_from(u64::from(word))
                .map(NodeIndex::from)
                .map_err(|_wider| untaken())
        };
        let indexed = action.try_map(
            ChildOrder::Forward,
            &mut (),
            |_state: &mut (), value| at(self.numbering.producer(value)?),
            |_state: &mut (), body| at(self.numbering.command(body)?),
            |_state: &mut (), ty| self.indexed(ty),
        )?;
        let mut buffer = annotations::Buffer::default();
        write_session_action(&mut NodeWriter { sink: &mut buffer }, &indexed)
            .map_err(|_unwritten| untaken())?;
        Ok(buffer)
    }

    /// Write the producers of `ids` after their count.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// The sink's refusal.
    fn producers<Sink>(
        &self,
        ids: &[ProducerId],
        sink: &mut Sink,
    ) -> Result<(), ValueError>
    where
        Sink: TokenSink + ?Sized,
    {
        sink.word(count(ids.len())?)?;
        ids.iter()
            .try_for_each(|&id| sink.word(self.numbering.producer(id)?))
    }

    /// Write the consumers of `ids` after their count.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// The sink's refusal.
    fn consumers<Sink>(
        &self,
        ids: &[ConsumerId],
        sink: &mut Sink,
    ) -> Result<(), ValueError>
    where
        Sink: TokenSink + ?Sized,
    {
        sink.word(count(ids.len())?)?;
        ids.iter()
            .try_for_each(|&id| sink.word(self.numbering.consumer(id)?))
    }

    /// Write a producer's open, payload and close.
    ///
    /// # Specification
    /// - requires: the producer is not a code, and its head crosses.
    /// - ensures: on success the node as the module's table states.
    /// - fails: the sink's refusal.
    /// - panics: none.
    /// - executable: none — the tag table is its own specification.
    ///
    /// # Errors
    /// The sink's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — as [`encode`].
    /// - witness: `tests::image::each_named_program_reads_back_and_runs_alike`
    fn emit_producer<Sink>(
        &self,
        node: &ProducerNode,
        sink: &mut Sink,
    ) -> Result<(), ValueError>
    where
        Sink: TokenSink + ?Sized,
    {
        let numbering = &self.numbering;
        match *node {
            ProducerNode::Reify(ref frames) => {
                sink.open(ConstructorTag::from(REIFY))?;
                sink.word(count(frames.len())?)?;
                for &frame in frames.iter() {
                    match frame {
                        StackFrame::Apply(value) => {
                            sink.word(CanonicalWord::from(0_u64))?;
                            sink.word(numbering.producer(value)?)?;
                        },
                        StackFrame::Bind(body) => {
                            sink.word(CanonicalWord::from(1_u64))?;
                            sink.word(numbering.command(body)?)?;
                        },
                        StackFrame::Project(component) => {
                            sink.word(CanonicalWord::from(2_u64))?;
                            sink.word(count(usize::from(component))?)?;
                        },
                    }
                }
            },
            ProducerNode::Primitive {
                primitive,
                ref arguments,
            } => {
                sink.open(ConstructorTag::from(PRIMITIVE))?;
                let row = PRELUDE
                    .iter()
                    .position(|&held| held == primitive)
                    .ok_or_else(untaken)?;
                sink.word(count(row)?)?;
                sink.word(count(arguments.len())?)?;
                arguments
                    .iter()
                    .try_for_each(|&argument| sink.word(numbering.producer(argument)?))?;
            },
            ProducerNode::Decompose(dialogue) => {
                sink.open(ConstructorTag::from(DECOMPOSE))?;
                sink.word(numbering.producer(dialogue)?)?;
            },
            ProducerNode::Variable { zone, index } => {
                sink.open(ConstructorTag::from(VARIABLE))?;
                sink.word(CanonicalWord::from(match zone {
                    Zone::Intuitionistic => 0_u64,
                    Zone::Linear => 1_u64,
                }))?;
                sink.word(position(u32::from(index)))?;
            },
            ProducerNode::Constant(constant) => {
                sink.open(ConstructorTag::from(CONSTANT))?;
                sink.word(count(usize::from(constant))?)?;
            },
            ProducerNode::Literal(ref literal) => {
                sink.open(ConstructorTag::from(LITERAL))?;
                emit_literal(literal, sink)?;
                sink.close()?;
            },
            ProducerNode::Code(value) => {
                sink.open(ConstructorTag::from(CODE))?;
                sink.word(position(self.ordinal(ArenaNode::Value(value))?))?;
            },
            ProducerNode::Constructor {
                ref tag,
                ref producers,
                ref consumers,
            } => {
                sink.open(ConstructorTag::from(CONSTRUCTOR))?;
                emit_head(tag, sink).map_err(|_uncrossable| untaken())??;
                sink.close()?;
                self.producers(producers, sink)?;
                self.consumers(consumers, sink)?;
            },
            ProducerNode::Thunk { body } => {
                sink.open(ConstructorTag::from(THUNK))?;
                sink.word(numbering.command(body)?)?;
            },
            ProducerNode::Fixpoint { body, evidence } => {
                sink.open(ConstructorTag::from(FIXPOINT))?;
                sink.word(numbering.command(body)?)?;
                match evidence {
                    FixpointEvidence::Partial => sink.word(CanonicalWord::from(0_u64))?,
                    FixpointEvidence::StructuralDescent => sink.word(CanonicalWord::from(1_u64))?,
                    FixpointEvidence::Staged { position } => {
                        sink.word(CanonicalWord::from(2_u64))?;
                        sink.word(count(usize::from(position))?)?;
                    },
                    FixpointEvidence::Joint { positions } => {
                        sink.word(CanonicalWord::from(3_u64))?;
                        sink.word(count(positions.iter().count())?)?;
                        positions
                            .iter()
                            .try_for_each(|position| sink.word(count(usize::from(position))?))?;
                    },
                    FixpointEvidence::Guarded => sink.word(CanonicalWord::from(4_u64))?,
                }
            },
            ProducerNode::Cocase { ref arms } => {
                sink.open(ConstructorTag::from(COCASE))?;
                sink.word(count(arms.len())?)?;
                for arm in arms {
                    emit_destructor(arm.destructor, sink)?;
                    sink.word(numbering.command(arm.body)?)?;
                }
            },
            ProducerNode::Closure {
                ref environment,
                code,
            } => {
                sink.open(ConstructorTag::from(CLOSURE))?;
                self.producers(environment, sink)?;
                sink.word(numbering.producer(code)?)?;
            },
            ProducerNode::Mu { body } => {
                sink.open(ConstructorTag::from(MU))?;
                sink.word(numbering.command(body)?)?;
            },
        }
        sink.close()
    }

    /// Write a consumer's open, payload and close.
    ///
    /// # Specification
    /// - requires: the consumer is not a fold, and each arm's head crosses.
    /// - ensures: on success the node as the module's table states.
    /// - fails: the sink's refusal.
    /// - panics: none.
    /// - executable: none — the tag table is its own specification.
    ///
    /// # Errors
    /// The sink's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — as [`encode`].
    /// - witness: `tests::image::each_named_program_reads_back_and_runs_alike`
    fn emit_consumer<Sink>(
        &self,
        node: &ConsumerNode,
        independence: Independence,
        sink: &mut Sink,
    ) -> Result<(), ValueError>
    where
        Sink: TokenSink + ?Sized,
    {
        let numbering = &self.numbering;
        match *node {
            ConsumerNode::Covariable(index) => {
                sink.open(ConstructorTag::from(COVARIABLE))?;
                sink.word(position(u32::from(index)))?;
            },
            ConsumerNode::MuTilde { body } => {
                sink.open(ConstructorTag::from(MU_TILDE))?;
                sink.word(CanonicalWord::from(match independence {
                    Independence::Sequential => 0_u64,
                    Independence::Independent => 1_u64,
                }))?;
                sink.word(numbering.command(body)?)?;
            },
            ConsumerNode::MuTildeAll { arity, body } => {
                sink.open(ConstructorTag::from(MU_TILDE_ALL))?;
                sink.word(count(usize::from(arity))?)?;
                sink.word(numbering.command(body)?)?;
            },
            ConsumerNode::Destructor {
                tag,
                ref producers,
                ref consumers,
            } => {
                sink.open(ConstructorTag::from(DESTRUCTOR))?;
                emit_destructor(tag, sink)?;
                self.producers(producers, sink)?;
                self.consumers(consumers, sink)?;
            },
            ConsumerNode::Case { ref arms } => {
                sink.open(ConstructorTag::from(CASE))?;
                sink.word(count(arms.len())?)?;
                for arm in arms {
                    emit_head(&arm.constructor, sink).map_err(|_uncrossable| untaken())??;
                    sink.close()?;
                    sink.word(numbering.command(arm.body)?)?;
                }
            },
            ConsumerNode::DataCase {
                ref branches,
                ref arities,
                then,
            } => {
                sink.open(ConstructorTag::from(DATA_CASE))?;
                self.producers(branches, sink)?;
                sink.word(count(arities.len())?)?;
                arities
                    .iter()
                    .try_for_each(|&arity| sink.word(count(usize::from(arity))?))?;
                sink.word(numbering.consumer(then)?)?;
            },
            ConsumerNode::Select { ref selector, then } => {
                sink.open(ConstructorTag::from(SELECT))?;
                match *selector {
                    Selector::Component(component) => {
                        sink.word(CanonicalWord::from(0_u64))?;
                        sink.word(count(usize::from(component))?)?;
                    },
                    Selector::Label(ref label) => {
                        sink.word(CanonicalWord::from(1_u64))?;
                        sink.bytes(TokenBytes::from(str::as_bytes(label.as_ref())))?;
                    },
                }
                sink.word(numbering.consumer(then)?)?;
            },
            ConsumerNode::ListFold {
                element,
                result,
                on_nil,
                on_cons,
                continuation,
            } => {
                sink.open(ConstructorTag::from(LIST_FOLD))?;
                sink.word(position(self.ordinal(ArenaNode::ValueType(element))?))?;
                sink.word(position(self.ordinal(ArenaNode::ValueType(result))?))?;
                sink.word(numbering.command(on_nil)?)?;
                sink.word(numbering.command(on_cons)?)?;
                sink.word(numbering.consumer(continuation)?)?;
            },
            ConsumerNode::Top => sink.open(ConstructorTag::from(TOP))?,
        }
        sink.close()
    }

    /// Write a command's open, payload and close.
    ///
    /// # Specification
    /// - requires: the command is not an operation, a handler or a session
    ///   action.
    /// - ensures: on success the node as the module's table states.
    /// - fails: the sink's refusal.
    /// - panics: none.
    /// - executable: none — the tag table is its own specification.
    ///
    /// # Errors
    /// The sink's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — as [`encode`].
    /// - witness: `tests::image::each_named_program_reads_back_and_runs_alike`
    fn emit_command<Sink>(
        &self,
        node: &CommandNode,
        sink: &mut Sink,
    ) -> Result<(), ValueError>
    where
        Sink: TokenSink + ?Sized,
    {
        let numbering = &self.numbering;
        match *node {
            CommandNode::Perform {
                ref signature,
                ref operation,
                route,
                payload,
                continuation,
            } => {
                sink.open(ConstructorTag::from(PERFORM))?;
                sink.bytes(TokenBytes::from(self.signature_bytes(signature)?.as_ref()))?;
                sink.bytes(TokenBytes::from(str::as_bytes(operation.as_ref())))?;
                match route {
                    Route::Nearest => sink.word(CanonicalWord::from(0_u64))?,
                    Route::Capability(capability) => {
                        sink.word(CanonicalWord::from(1_u64))?;
                        sink.word(numbering.producer(capability)?)?;
                    },
                }
                sink.word(numbering.producer(payload)?)?;
                sink.word(numbering.consumer(continuation)?)?;
            },
            CommandNode::Handle {
                ref signature,
                introduces,
                subject,
                on_return,
                ref clauses,
                continuation,
            } => {
                sink.open(ConstructorTag::from(HANDLE))?;
                sink.bytes(TokenBytes::from(self.signature_bytes(signature)?.as_ref()))?;
                sink.word(CanonicalWord::from(match introduces {
                    Introduces::Nothing => 0_u64,
                    Introduces::Capability => 1_u64,
                }))?;
                sink.word(numbering.command(subject)?)?;
                sink.word(numbering.command(on_return)?)?;
                sink.word(count(clauses.len())?)?;
                for clause in clauses.iter() {
                    sink.bytes(TokenBytes::from(str::as_bytes(clause.operation.as_ref())))?;
                    sink.word(numbering.command(clause.body)?)?;
                }
                sink.word(numbering.consumer(continuation)?)?;
            },
            CommandNode::Session {
                ref action,
                continuation,
            } => {
                sink.open(ConstructorTag::from(SESSION))?;
                sink.bytes(TokenBytes::from(self.action_bytes(action)?.as_ref()))?;
                sink.word(numbering.consumer(continuation)?)?;
            },
            CommandNode::Resume {
                stack,
                body,
                continuation,
            } => {
                sink.open(ConstructorTag::from(RESUME))?;
                sink.word(numbering.producer(stack)?)?;
                sink.word(numbering.command(body)?)?;
                sink.word(numbering.consumer(continuation)?)?;
            },
            CommandNode::Abandon {
                stack,
                continuation,
            } => {
                sink.open(ConstructorTag::from(ABANDON))?;
                sink.word(numbering.producer(stack)?)?;
                sink.word(numbering.consumer(continuation)?)?;
            },
            CommandNode::Reset { body, continuation } => {
                sink.open(ConstructorTag::from(RESET))?;
                sink.word(numbering.command(body)?)?;
                sink.word(numbering.consumer(continuation)?)?;
            },
            CommandNode::Shift { body, continuation } => {
                sink.open(ConstructorTag::from(SHIFT))?;
                sink.word(numbering.command(body)?)?;
                sink.word(numbering.consumer(continuation)?)?;
            },
            CommandNode::Cut {
                polarity,
                producer,
                consumer,
            } => {
                sink.open(ConstructorTag::from(CUT))?;
                sink.word(CanonicalWord::from(match polarity {
                    Polarity::Positive => 0_u64,
                    Polarity::Negative => 1_u64,
                }))?;
                sink.word(numbering.producer(producer)?)?;
                sink.word(numbering.consumer(consumer)?)?;
            },
            CommandNode::Deliver {
                ref producers,
                consumer,
            } => {
                sink.open(ConstructorTag::from(DELIVER))?;
                self.producers(producers, sink)?;
                sink.word(numbering.consumer(consumer)?)?;
            },
            CommandNode::Memory {
                ref form,
                continuation,
            } => {
                sink.open(ConstructorTag::from(MEMORY))?;
                self.emit_memory(form, sink)?;
                sink.word(numbering.consumer(continuation)?)?;
            },
            CommandNode::World { form, continuation } => {
                sink.open(ConstructorTag::from(WORLD))?;
                match form {
                    WorldForm::Hold { value } => {
                        sink.word(CanonicalWord::from(0_u64))?;
                        sink.word(numbering.producer(value)?)?;
                    },
                    WorldForm::Leta { world, value, body } => {
                        sink.word(CanonicalWord::from(1_u64))?;
                        emit_world(world, sink)?;
                        sink.word(numbering.producer(value)?)?;
                        sink.word(numbering.command(body)?)?;
                    },
                    WorldForm::Migrate { world, body } => {
                        sink.word(CanonicalWord::from(2_u64))?;
                        emit_world(world, sink)?;
                        sink.word(numbering.command(body)?)?;
                    },
                }
                sink.word(numbering.consumer(continuation)?)?;
            },
        }
        sink.close()
    }

    /// Write a memory form's case and operands.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// The sink's refusal.
    fn emit_memory<Sink>(
        &self,
        form: &MemoryForm<ProducerId, CommandId>,
        sink: &mut Sink,
    ) -> Result<(), ValueError>
    where
        Sink: TokenSink + ?Sized,
    {
        let numbering = &self.numbering;
        match *form {
            MemoryForm::Hold { value, body, grade } => {
                sink.word(CanonicalWord::from(0_u64))?;
                sink.word(numbering.producer(value)?)?;
                sink.word(numbering.command(body)?)?;
                sink.word(CanonicalWord::from(match grade {
                    HoldGrade::Many => 0_u64,
                    HoldGrade::One => 1_u64,
                }))
            },
            MemoryForm::Access {
                mode,
                held,
                place,
                body,
            } => {
                sink.word(CanonicalWord::from(1_u64))?;
                match mode {
                    AccessMode::Shared => sink.word(CanonicalWord::from(0_u64))?,
                    AccessMode::Exclusive { unwind } => {
                        sink.word(CanonicalWord::from(1_u64))?;
                        sink.word(numbering.command(unwind)?)?;
                    },
                }
                sink.word(position(u32::from(held)))?;
                match place {
                    Place::Whole => sink.word(CanonicalWord::from(0_u64))?,
                    Place::At { index } => {
                        sink.word(CanonicalWord::from(1_u64))?;
                        sink.word(numbering.producer(index)?)?;
                    },
                }
                sink.word(numbering.command(body)?)
            },
            MemoryForm::Resume { view, value } => {
                sink.word(CanonicalWord::from(2_u64))?;
                sink.word(position(u32::from(view)))?;
                sink.word(numbering.producer(value)?)
            },
            MemoryForm::Abort { view } => {
                sink.word(CanonicalWord::from(3_u64))?;
                sink.word(position(u32::from(view)))
            },
            MemoryForm::Consume { held } => {
                sink.word(CanonicalWord::from(4_u64))?;
                sink.word(position(u32::from(held)))
            },
        }
    }
}

/// Write a destructor head: its case, then a projection's component.
///
/// # Specification
/// trivial.
///
/// # Errors
/// The sink's refusal.
fn emit_destructor<Sink>(
    head: DestructorTag,
    sink: &mut Sink,
) -> Result<(), ValueError>
where
    Sink: TokenSink + ?Sized,
{
    match head {
        DestructorTag::Apply => sink.word(CanonicalWord::from(0_u64)),
        DestructorTag::Force => sink.word(CanonicalWord::from(1_u64)),
        DestructorTag::Project(component) => {
            sink.word(CanonicalWord::from(2_u64))?;
            sink.word(count(usize::from(component))?)
        },
    }
}

/// Write a world: zero for the host's, or one and the declaration's
/// position.
///
/// # Specification
/// trivial.
///
/// # Errors
/// The sink's refusal.
fn emit_world<Sink>(
    world: World,
    sink: &mut Sink,
) -> Result<(), ValueError>
where
    Sink: TokenSink + ?Sized,
{
    match world {
        World::Host => sink.word(CanonicalWord::from(0_u64)),
        World::Declared(constant) => {
            sink.word(CanonicalWord::from(1_u64))?;
            sink.word(count(usize::from(constant))?)
        },
    }
}
