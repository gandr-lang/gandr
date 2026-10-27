//! A run's value crossing between worlds by content: [`commit`] writes the
//! value a [`Store`] binds onto the value plane, and [`deref()`] reads it back
//! into a [`Store`] at addresses fresh there.
//!
//! The two ends share no location. What crosses is what the checker's `Open`
//! admits at run time: a literal of every kind, and a tuple, a record, a list,
//! an injection, a lift or a datatype's constructor over fields that cross.
//! Each head is one constructor on the plane: its tag, its payload in the
//! records after its open, then its fields, then its close. Any other value is
//! refused by name before anything is written ([`Uncrossable`]).
//!
//! # Boundaries
//!
//! - **Sharing unfolds.** The encoding is the same however the source shares,
//!   so a value two fields hold is written twice, its chunks stored once by
//!   content, and a deref lays out a tree. A pair shared at twenty levels,
//!   twenty-one values, writes 7,340,029 records into 5 chunks and derefs to
//!   2,097,151 values, in about half a second each way on a release build.
//!   Sharing kept across a crossing needs a child pointer per shared value.
//! - **One program.** A family crosses as its declaration's index, which names
//!   one declaration at both ends because both run one program. A crossing
//!   between processes names it by content.
//! - **The constants are the deployment's.** The codec owns its identity and
//!   the plane's classification, every constructor a cut candidate; the
//!   chunker's constants are the caller's, pinned by the deployment that
//!   measures its values ([`profile`]).
//! - **A payload is its constructor's.** A payload the codec does not write —
//!   digits that are not digits, a character that is not one scalar, a width
//!   pattern wider than its width, labels out of their order — refuses its
//!   constructor at its open record, as the plane refuses a tag no codec
//!   admits.
//!
//! # References
//!
//! - `Rainey-2026-localmem_typedirected_adaptive_serialization_location_contentaddressable_memory` — background: a
//!   crossing as § 5's `CAMCommit` then `CAMDeref` between two LAMs through
//!   one CAM, the canonical encoding and the round trip (Lemma 5.7) this codec
//!   is held to.
//! - `vault:01a178ab-17e5-7352-bc0b-3caa7f1e476c` — lineage: the storage
//!   programme, § storage-programme-worlds-sessions: `Open` is representation,
//!   and the canonical codec is its witness.

use alloc::borrow::Cow;
use alloc::boxed::Box;
use alloc::string::String;
use alloc::sync::Arc;
use alloc::vec::Vec;

use gandr_core_sequent::ConstructorTag as Head;
use gandr_core_sequent::HeapValue;
use gandr_core_sequent::HeapValueId;
use gandr_core_sequent::ProducerArity;
use gandr_core_sequent::Store;
use gandr_core_sequent::StoreFault;
use gandr_core_term::FieldLabel;
use gandr_kernel_strata::Level;
use gandr_kernel_strata::LevelConstant;
use gandr_kernel_strata::LevelVar;
use gandr_kernel_strata::LevelVarIndex;
use gandr_kernel_term::CharacterLiteral;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::FixedInteger;
use gandr_kernel_term::Float64Literal;
use gandr_kernel_term::FractionDigits;
use gandr_kernel_term::IntegerLiteral;
use gandr_kernel_term::IntegerWidth;
use gandr_kernel_term::Literal;
use gandr_kernel_term::Magnitude;
use gandr_kernel_term::NumericLiteral;
use gandr_kernel_term::Sign;
use gandr_kernel_term::StringLiteral;
use gandr_kernel_term::Summand;
use gandr_storage_chunker::TypedChunkerParams;
use gandr_storage_values::CanonicalValue;
use gandr_storage_values::CanonicalWord;
use gandr_storage_values::ChildIndexBase;
use gandr_storage_values::ChunkStore;
use gandr_storage_values::CodecId;
use gandr_storage_values::CodecIdentity;
use gandr_storage_values::CodecVersion;
use gandr_storage_values::ConstructorTag;
use gandr_storage_values::TokenBytes;
use gandr_storage_values::TokenOffset;
use gandr_storage_values::TokenReader;
use gandr_storage_values::TokenSink;
use gandr_storage_values::ValueError;
use gandr_storage_values::ValueManifest;
use gandr_storage_values::ValueProfile;
use gandr_storage_values::ValueQuantity;
use gandr_storage_values::cam_commit;

/// The codec's identifier among the value plane's codecs; domhringr's lines
/// codec holds 1.
const CODEC: u16 = 0x0002_u16;

/// The codec's layout version.
const CODEC_VERSION: u16 = 0x0001_u16;

/// An integer: its sign as a word, zero when non-negative, then its decimal
/// digits.
const INTEGER: u8 = 0x01_u8;

/// Text: its UTF-8 bytes.
const TEXT: u8 = 0x02_u8;

/// A decimal numeric: its sign as an integer's is, then its integral and its
/// fractional digits.
const NUMERIC: u8 = 0x03_u8;

/// A character: its scalar as a word.
const CHARACTER: u8 = 0x04_u8;

/// A floating-point number: its bit pattern as a word.
const FLOAT: u8 = 0x05_u8;

/// A width integer: its width as a word — `u32`, `u64`, `i32`, `i64` from zero
/// — then its bit pattern.
const FIXED: u8 = 0x06_u8;

/// A tuple: its arity, then its fields.
const TUPLE: u8 = 0x10_u8;

/// A record: its label count, then each label's UTF-8 bytes in their order,
/// then one field per label.
const RECORD: u8 = 0x11_u8;

/// The empty list.
const NIL: u8 = 0x12_u8;

/// A list cell: its head, then its tail.
const CONS: u8 = 0x13_u8;

/// An injection: its summand, then its field.
const INJECTION: u8 = 0x14_u8;

/// A lift: its level's constant, its atom count and each atom's variable and
/// offset, then its field.
const LIFT: u8 = 0x15_u8;

/// A datatype's constructor naming no family: its ordinal and its arity, then
/// its fields.
const DATA: u8 = 0x16_u8;

/// A datatype's constructor of a named family: its ordinal, its arity and its
/// family's declaration index, then its fields.
const FAMILY_DATA: u8 = 0x17_u8;

/// A value that does not cross, by what it is.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Uncrossable
{
    /// A literal stack: its frames are a run's code.
    Stack,
    /// A thunk: its body is a command in the arena that lowered it.
    Thunk,
    /// A recursive thunk, as a thunk.
    Fixpoint,
    /// A copattern object or a captured context, as a thunk.
    Closure,
    /// A constant with no body, which a run carries but never reads.
    Opaque,
    /// A code: static content, judged where it stands.
    Code,
    /// A capability: authority, never data.
    Capability,
    /// A recorded run.
    Recorded,
    /// A dialogue.
    Dialogue,
    /// A web.
    Web,
}

/// Why a value did not cross.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CrossingRefusal
{
    /// The value holds one that does not cross, at this address.
    Uncrossable
    {
        /// The value that does not cross.
        value: HeapValueId,
        /// What it is.
        head: Uncrossable,
    },
    /// The store binds nothing at an address the value reaches.
    Unbound(HeapValueId),
    /// The value plane refused: a profile other than the reader's, a chunk
    /// missing or invalid, or a record or constructor the codec does not read.
    Plane(ValueError),
    /// The destination store refused an allocation.
    Store(StoreFault),
}

impl From<ValueError> for CrossingRefusal
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

impl From<StoreFault> for CrossingRefusal
{
    /// The store's refusal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(fault: StoreFault) -> Self
    {
        Self::Store(fault)
    }
}

/// The profile a crossing commits and reads under: the chunker at `params`,
/// this codec's identity, absolute child indices, every constructor a cut
/// candidate.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the profile's chunker parameters are `params` and its codec is
///   this codec's; two calls with equal parameters answer equal profiles.
/// - provides: the one profile a [`commit`] writes and a [`deref()`] expects,
///   for a deployment that pins its constants.
/// - panics: none.
/// - executable: none — the constructor is its own specification.
///
/// # Adequacy
/// - hypothesis: L3 — a value committed under one pair of constants derefs
///   under the same pair, and one read under another pair is refused naming the
///   chunker's commitment.
/// - witness: `tests::crossing::every_crossing_head_commits_and_derefs_back_equal`
/// - witness: `tests::crossing::a_value_read_under_other_constants_is_refused`
#[inline]
#[must_use]
pub fn profile(params: TypedChunkerParams) -> ValueProfile
{
    ValueProfile::new(
        params,
        CodecIdentity::new(CodecId::from(CODEC), CodecVersion::from(CODEC_VERSION)),
        ChildIndexBase::Absolute,
    )
}

/// Commit the value `store` binds at `value` to `chunks`, under [`profile`]
/// at `params`.
///
/// # Specification
/// - requires: nothing; a value that does not cross is refused.
/// - ensures: on success the manifest of the value's canonical encoding, its
///   chunks inserted into `chunks`; equal values commit to one root however
///   their stores share or place them. On a refusal nothing is inserted.
/// - executable: none — equality of the committed value is the round trip's,
///   which needs a store to read it back into.
///
/// # Errors
/// [`CrossingRefusal::Uncrossable`] naming the first value in preorder that
/// does not cross; [`CrossingRefusal::Unbound`] for an address `store` does
/// not bind; [`CrossingRefusal::Plane`] for the plane's refusal of the
/// encoding.
///
/// # Adequacy
/// - hypothesis: L2 — every crossing head, every literal kind and nested values
///   commit and deref back equal, into an empty store and one already holding
///   values; one value built in two stores, shared and unshared, commits to one
///   root. L3 — each value that does not cross, held in a tuple's field, is
///   refused naming it, with no chunk written.
/// - witness: `tests::crossing::every_crossing_head_commits_and_derefs_back_equal`
/// - witness: `tests::crossing::one_value_commits_to_one_root_from_any_store`
/// - witness: `tests::crossing::a_value_that_does_not_cross_is_refused_by_name_and_writes_nothing`
#[inline]
pub fn commit<Chunks>(
    store: &Store,
    value: HeapValueId,
    params: TypedChunkerParams,
    chunks: &mut Chunks,
) -> Result<ValueManifest, CrossingRefusal>
where
    Chunks: ChunkStore + ?Sized,
{
    let crossing = Crossing::of(store, value)?;
    Ok(cam_commit(chunks, &profile(params), &crossing)?)
}

/// Read the value `manifest` commits back into `store`, expecting [`profile`]
/// at `params`, and answer its root's address there.
///
/// # Specification
/// - requires: `chunks` holds the value's chunks, or refuses for those it does
///   not.
/// - ensures: on success the root of a tree of values freshly allocated in
///   `store`, equal to the committed value; a value shared in the committed one
///   is laid out once per occurrence.
/// - executable: none — as [`commit`].
///
/// # Errors
/// [`CrossingRefusal::Plane`] for a profile other than the expected one,
/// before any chunk is read, then for a chunk missing or invalid and for a
/// record or payload the codec does not read; [`CrossingRefusal::Store`] for
/// an allocation `store` refuses.
///
/// # Adequacy
/// - hypothesis: L2 — as [`commit`]; a shared value derefs to distinct equal
///   values, and a list of fifty thousand cells crosses whole. L3 — a payload
///   the codec does not write refuses its constructor at its open record.
/// - witness: `tests::crossing::every_crossing_head_commits_and_derefs_back_equal`
/// - witness: `tests::crossing::a_shared_value_derefs_unshared_and_equal`
/// - witness: `tests::crossing::a_long_list_crosses`
/// - witness: `tests::crossing::a_payload_the_codec_does_not_write_refuses_its_constructor`
#[inline]
pub fn deref(
    manifest: &ValueManifest,
    params: TypedChunkerParams,
    chunks: &dyn ChunkStore,
    store: &mut Store,
) -> Result<HeapValueId, CrossingRefusal>
{
    let crossing: Crossing<'static> = manifest.read_under(chunks, &profile(params))?;
    Ok(crossing.lay(store)?)
}

/// A constructor head that crosses: the core's positive heads but a session's.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug)]
enum Crossed<'store>
{
    /// A tuple of this many fields.
    Tuple(ProducerArity),
    /// A record, one field per label.
    Record(Arc<[FieldLabel]>),
    /// The empty list.
    Nil,
    /// A list cell.
    Cons,
    /// An injection into this summand.
    Injection(Summand),
    /// A lift to this level.
    Lift(Cow<'store, Level>),
    /// A datatype's constructor.
    Data
    {
        /// Its ordinal in its declaration.
        tag: gandr_kernel_term::ConstructorTag,
        /// The fields it carries.
        arity: ProducerArity,
        /// Its family's declaration, when the core named one.
        family: Option<ConstantIndex>,
    },
}

impl<'store> Crossed<'store>
{
    /// The crossing form of `head`.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// What the head is, when it does not cross: a recorded run, a dialogue or
    /// a web.
    fn of(head: &'store Head) -> Result<Self, Uncrossable>
    {
        Ok(match *head {
            Head::Tuple(arity) => Self::Tuple(arity),
            Head::Record(ref labels) => Self::Record(Arc::clone(labels)),
            Head::ListNil => Self::Nil,
            Head::ListCons => Self::Cons,
            Head::Injection(summand) => Self::Injection(summand),
            Head::Lift(ref level) => Self::Lift(Cow::Borrowed(level)),
            Head::Data { tag, arity, family } => Self::Data { tag, arity, family },
            Head::Recorded(_) => return Err(Uncrossable::Recorded),
            Head::Dialogue(_) => return Err(Uncrossable::Dialogue),
            Head::Web(_) => return Err(Uncrossable::Web),
        })
    }

    /// The head it is.
    ///
    /// # Specification
    /// trivial.
    fn into_head(self) -> Head
    {
        match self {
            Self::Tuple(arity) => Head::Tuple(arity),
            Self::Record(labels) => Head::Record(labels),
            Self::Nil => Head::ListNil,
            Self::Cons => Head::ListCons,
            Self::Injection(summand) => Head::Injection(summand),
            Self::Lift(level) => Head::Lift(level.into_owned()),
            Self::Data { tag, arity, family } => Head::Data { tag, arity, family },
        }
    }

    /// How many fields the head carries, as its payload states them.
    ///
    /// # Specification
    /// trivial.
    fn fields(&self) -> Count
    {
        Count(match *self {
            Self::Nil => 0_usize,
            Self::Cons => 2_usize,
            Self::Injection(_) | Self::Lift(_) => 1_usize,
            Self::Tuple(arity) | Self::Data { arity, .. } => usize::from(arity),
            Self::Record(ref labels) => labels.len(),
        })
    }

    /// Write the head's open and payload.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the head's open, then its payload as its tag states.
    /// - fails: the sink's refusal.
    /// - panics: none.
    /// - executable: none — the tag table is its own specification.
    ///
    /// # Errors
    /// The first [`ValueError`] the sink returns.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every crossing head round-trips.
    /// - witness: `tests::crossing::every_crossing_head_commits_and_derefs_back_equal`
    fn emit<Sink>(
        &self,
        sink: &mut Sink,
    ) -> Result<(), ValueError>
    where
        Sink: TokenSink + ?Sized,
    {
        match *self {
            Self::Tuple(arity) => {
                sink.open(ConstructorTag::from(TUPLE))?;
                sink.word(count_word(Count(usize::from(arity)))?)
            },
            Self::Record(ref labels) => {
                sink.open(ConstructorTag::from(RECORD))?;
                sink.word(count_word(Count(labels.len()))?)?;
                labels.iter().try_for_each(|label| {
                    sink.bytes(TokenBytes::from(str::as_bytes(label.as_ref())))
                })
            },
            Self::Nil => sink.open(ConstructorTag::from(NIL)),
            Self::Cons => sink.open(ConstructorTag::from(CONS)),
            Self::Injection(summand) => {
                sink.open(ConstructorTag::from(INJECTION))?;
                sink.word(count_word(Count(usize::from(summand)))?)
            },
            Self::Lift(ref level) => {
                sink.open(ConstructorTag::from(LIFT))?;
                sink.word(CanonicalWord::from(u64::from(level.constant_part())))?;
                sink.word(count_word(Count(level.atoms().count()))?)?;
                level.atoms().try_for_each(|(variable, offset)| {
                    sink.word(CanonicalWord::from(u64::from(u32::from(variable.index()))))?;
                    sink.word(CanonicalWord::from(u64::from(offset)))
                })
            },
            Self::Data { tag, arity, family } => {
                sink.open(ConstructorTag::from(match family {
                    None => DATA,
                    Some(_) => FAMILY_DATA,
                }))?;
                sink.word(count_word(Count(usize::from(tag)))?)?;
                sink.word(count_word(Count(usize::from(arity)))?)?;
                family.map_or(Ok(()), |family| {
                    sink.word(count_word(Count(usize::from(family)))?)
                })
            },
        }
    }
}

/// One head of a crossing value: a literal, or a constructor whose fields
/// follow it.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug)]
enum Node<'store>
{
    /// A literal: a leaf.
    Literal(Cow<'store, Literal>),
    /// A constructor, its fields the values after it in preorder.
    Constructed(Crossed<'store>),
}

impl<'store> Node<'store>
{
    /// The node of the value `store` binds at `id`, its fields owed to
    /// `pending` first field on top.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// [`CrossingRefusal::Uncrossable`] naming `id` when its value does not
    /// cross, and [`CrossingRefusal::Unbound`] when `store` binds nothing
    /// there.
    fn of(
        store: &'store Store,
        id: HeapValueId,
        pending: &mut Vec<HeapValueId>,
    ) -> Result<Self, CrossingRefusal>
    {
        let refused = |head| CrossingRefusal::Uncrossable { value: id, head };
        Ok(
            match *store.value(id).ok_or(CrossingRefusal::Unbound(id))? {
                HeapValue::Literal(ref literal) => Self::Literal(Cow::Borrowed(literal)),
                HeapValue::Constructed {
                    ref tag,
                    ref fields,
                } => {
                    let crossed = Crossed::of(tag).map_err(refused)?;
                    pending.extend(fields.iter().rev().copied());
                    Self::Constructed(crossed)
                },
                HeapValue::Stack { .. } => return Err(refused(Uncrossable::Stack)),
                HeapValue::Thunk { .. } => return Err(refused(Uncrossable::Thunk)),
                HeapValue::Fixpoint { .. } => return Err(refused(Uncrossable::Fixpoint)),
                HeapValue::Closure { .. } => return Err(refused(Uncrossable::Closure)),
                HeapValue::Opaque(_) => return Err(refused(Uncrossable::Opaque)),
                HeapValue::Code(_) => return Err(refused(Uncrossable::Code)),
                HeapValue::Capability => return Err(refused(Uncrossable::Capability)),
            },
        )
    }

    /// How many values follow this one as its fields.
    ///
    /// # Specification
    /// trivial.
    fn fields(&self) -> Count
    {
        match *self {
            Self::Literal(_) => Count(0_usize),
            Self::Constructed(ref crossed) => crossed.fields(),
        }
    }

    /// Write the node's open and payload.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// The first [`ValueError`] the sink returns.
    fn emit<Sink>(
        &self,
        sink: &mut Sink,
    ) -> Result<(), ValueError>
    where
        Sink: TokenSink + ?Sized,
    {
        match *self {
            Self::Literal(ref literal) => emit_literal(literal, sink),
            Self::Constructed(ref crossed) => crossed.emit(sink),
        }
    }

    /// The store value of this node, its fields taken from the top of `laid`.
    ///
    /// # Specification
    /// - requires: `laid` holds at least this node's fields, its first field on
    ///   top.
    /// - ensures: the literal, or the constructed value over the fields popped
    ///   in order.
    /// - panics: none.
    /// - executable: none — the pop is its own specification.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — as [`deref()`].
    /// - witness: `tests::crossing::every_crossing_head_commits_and_derefs_back_equal`
    fn into_value(
        self,
        laid: &mut Vec<HeapValueId>,
    ) -> HeapValue
    {
        match self {
            Self::Literal(literal) => HeapValue::Literal(literal.into_owned()),
            Self::Constructed(crossed) => {
                let first = laid.len().saturating_sub(crossed.fields().0);
                // The first field was laid last, so it stands on top.
                let fields: Box<[HeapValueId]> = laid.drain(first ..).rev().collect();
                HeapValue::Constructed {
                    tag: crossed.into_head(),
                    fields,
                }
            },
        }
    }
}

/// A crossing value: its root, then the values below it in preorder, each
/// constructor followed by its fields, as the plane writes it. Borrowed from
/// the store it is committed out of, owned once read back.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug)]
struct Crossing<'store>
{
    /// The root.
    root: Node<'store>,
    /// The values below it, in preorder.
    below: Vec<Node<'store>>,
}

impl<'store> Crossing<'store>
{
    /// The value `store` binds at `root`, every value it reaches checked to
    /// cross.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success one node per value the root reaches, counted once
    ///   per occurrence, in preorder with fields left to right.
    /// - fails: the first value in preorder that does not cross, or an address
    ///   `store` does not bind.
    /// - panics: none.
    /// - executable: none — the walk is its own specification.
    /// - intension: an explicit worklist, so a deep value needs no deep stack.
    ///
    /// # Errors
    /// [`CrossingRefusal::Uncrossable`] and [`CrossingRefusal::Unbound`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`commit`].
    /// - witness: `tests::crossing::a_value_that_does_not_cross_is_refused_by_name_and_writes_nothing`
    /// - witness: `tests::crossing::a_long_list_crosses`
    fn of(
        store: &'store Store,
        root: HeapValueId,
    ) -> Result<Self, CrossingRefusal>
    {
        let mut pending = Vec::new();
        let root = Node::of(store, root, &mut pending)?;
        let mut below = Vec::new();
        while let Some(id) = pending.pop() {
            below.push(Node::of(store, id, &mut pending)?);
        }
        Ok(Self { root, below })
    }

    /// Allocate the value in `store`, children before parents, and answer its
    /// root.
    ///
    /// # Specification
    /// - requires: the nodes are one value in preorder, each constructor
    ///   followed by as many values as its head carries, as
    ///   [`Crossing::decode_tokens`] reads them.
    /// - ensures: on success one fresh value in `store` per node, each
    ///   constructor's fields the values its fields' nodes laid, left to right.
    /// - fails: the store's refusal.
    /// - panics: none.
    /// - executable: none — the fold is its own specification.
    /// - intension: the nodes in reverse with a stack of laid values, so a deep
    ///   value needs no deep stack.
    ///
    /// # Errors
    /// [`StoreFault`] — an allocation `store` refuses.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — as [`deref()`].
    /// - witness: `tests::crossing::every_crossing_head_commits_and_derefs_back_equal`
    /// - witness: `tests::crossing::a_long_list_crosses`
    fn lay(
        self,
        store: &mut Store,
    ) -> Result<HeapValueId, StoreFault>
    {
        let mut laid: Vec<HeapValueId> = Vec::new();
        for node in self.below.into_iter().rev() {
            let value = node.into_value(&mut laid);
            laid.push(store.allocate(value)?);
        }
        let root = self.root.into_value(&mut laid);
        store.allocate(root)
    }
}

impl CanonicalValue for Crossing<'_>
{
    /// Write each node's open and payload, closing a constructor once its
    /// last field has closed.
    ///
    /// # Specification
    /// - requires: the nodes are one value in preorder.
    /// - ensures: on success one balanced value: each node's open, payload,
    ///   fields and close.
    /// - fails: the sink's refusal.
    /// - panics: none.
    /// - executable: none — the walk is its own specification.
    ///
    /// # Errors
    /// The first [`ValueError`] the sink returns.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — as [`commit`].
    /// - witness: `tests::crossing::every_crossing_head_commits_and_derefs_back_equal`
    fn emit_tokens<Sink>(
        &self,
        sink: &mut Sink,
    ) -> Result<(), ValueError>
    where
        Sink: TokenSink + ?Sized,
    {
        let mut owed: Vec<usize> = Vec::new();
        for node in core::iter::once(&self.root).chain(&self.below) {
            node.emit(sink)?;
            let fields = node.fields().0;
            if fields > 0_usize {
                owed.push(fields);
                continue;
            }
            sink.close()?;
            while let Some(left) = owed.last_mut() {
                *left = left.saturating_sub(1_usize);
                if *left > 0_usize {
                    break;
                }
                let _closed = owed.pop();
                sink.close()?;
            }
        }
        Ok(())
    }

    /// Read nodes until the root closes, each constructor owed as many
    /// values as its head carries.
    ///
    /// # Specification
    /// - requires: `reader` stands at the value's root.
    /// - ensures: on success the value's nodes in preorder, every literal and
    ///   head owned, the reader past the root's close.
    /// - fails: the reader's refusal, and a tag or payload the codec does not
    ///   write refused as its constructor at its open record.
    /// - panics: none.
    /// - executable: none — the walk is its own specification.
    ///
    /// # Errors
    /// [`ValueError`]: as listed above.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — as [`deref()`]; L3 — a malformed payload of each kind
    ///   that has one is refused at its open record.
    /// - witness: `tests::crossing::every_crossing_head_commits_and_derefs_back_equal`
    /// - witness: `tests::crossing::a_payload_the_codec_does_not_write_refuses_its_constructor`
    fn decode_tokens(reader: &mut TokenReader<'_>) -> Result<Self, ValueError>
    {
        let root = Opened::read(reader)?;
        let mut fields = root.fields().0;
        let mut below = Vec::new();
        let mut owed: Vec<usize> = Vec::new();
        loop {
            if fields > 0_usize {
                owed.push(fields);
            }
            else {
                reader.read_close()?;
                loop {
                    let Some(left) = owed.last_mut()
                    else {
                        return Ok(Self { root, below });
                    };
                    *left = left.saturating_sub(1_usize);
                    if *left > 0_usize {
                        break;
                    }
                    let _closed = owed.pop();
                    reader.read_close()?;
                }
            }
            let node = Opened::read(reader)?;
            fields = node.fields().0;
            below.push(node);
        }
    }
}

/// A count, an ordinal or an index, which a payload states as one word.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Count(usize);

/// A count as the plane's word.
///
/// # Specification
/// trivial.
///
/// # Errors
/// [`ValueError::ArithmeticOverflow`] for a count wider than a word, which no
/// host this crate builds for has.
fn count_word(count: Count) -> Result<CanonicalWord, ValueError>
{
    u64::try_from(count.0)
        .map(CanonicalWord::from)
        .map_err(|_wider| ValueError::ArithmeticOverflow {
            quantity: ValueQuantity::TokenCount,
        })
}

/// A sign as its word: zero when non-negative.
///
/// # Specification
/// trivial.
fn sign_word(sign: Sign) -> CanonicalWord
{
    CanonicalWord::from(match sign {
        Sign::NonNegative => 0_u64,
        Sign::Negative => 1_u64,
    })
}

/// A width as its word, `u32`, `u64`, `i32`, `i64` from zero.
///
/// # Specification
/// trivial.
fn width_word(width: IntegerWidth) -> CanonicalWord
{
    CanonicalWord::from(match width {
        IntegerWidth::U32 => 0_u64,
        IntegerWidth::U64 => 1_u64,
        IntegerWidth::I32 => 2_u64,
        IntegerWidth::I64 => 3_u64,
    })
}

/// Write a literal's open and payload.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the literal's kind's open, then its payload as its tag states.
/// - fails: the sink's refusal.
/// - panics: none.
/// - executable: none — the tag table is its own specification.
///
/// # Errors
/// The first [`ValueError`] the sink returns.
///
/// # Adequacy
/// - hypothesis: L2 — every literal kind round-trips.
/// - witness: `tests::crossing::every_crossing_head_commits_and_derefs_back_equal`
fn emit_literal<Sink>(
    literal: &Literal,
    sink: &mut Sink,
) -> Result<(), ValueError>
where
    Sink: TokenSink + ?Sized,
{
    match *literal {
        Literal::Integer(ref integer) => {
            sink.open(ConstructorTag::from(INTEGER))?;
            sink.word(sign_word(integer.sign()))?;
            sink.bytes(TokenBytes::from(str::as_bytes(
                integer.magnitude().as_ref(),
            )))
        },
        Literal::Text(ref text) => {
            sink.open(ConstructorTag::from(TEXT))?;
            sink.bytes(TokenBytes::from(str::as_bytes(text.as_ref())))
        },
        Literal::Numeric(ref numeric) => {
            sink.open(ConstructorTag::from(NUMERIC))?;
            sink.word(sign_word(numeric.sign()))?;
            sink.bytes(TokenBytes::from(str::as_bytes(
                numeric.integer_part().as_ref(),
            )))?;
            sink.bytes(TokenBytes::from(str::as_bytes(numeric.fraction().as_ref())))
        },
        Literal::Character(character) => {
            sink.open(ConstructorTag::from(CHARACTER))?;
            let scalar = char::from(character);
            sink.word(CanonicalWord::from(u64::from(u32::from(scalar))))
        },
        Literal::Float64(float) => {
            sink.open(ConstructorTag::from(FLOAT))?;
            sink.word(CanonicalWord::from(u64::from(float)))
        },
        Literal::Fixed(fixed) => {
            sink.open(ConstructorTag::from(FIXED))?;
            sink.word(width_word(fixed.width()))?;
            sink.word(CanonicalWord::from(u64::from(fixed)))
        },
    }
}

/// A constructor's open record, read: its tag and where it stands, which a
/// refusal of its payload names.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug)]
struct Opened
{
    /// The record position of the open.
    at: TokenOffset,
    /// The tag it opened with.
    tag: ConstructorTag,
}

impl Opened
{
    /// Read an open record and the payload its tag states, and answer its
    /// node.
    ///
    /// # Specification
    /// - requires: the reader stands at an open record.
    /// - ensures: on success the node the tag and payload name, the reader
    ///   after the payload.
    /// - fails: the reader's refusal, and this constructor's for a tag the
    ///   codec does not write, a word wider than its field, text that is not
    ///   UTF-8, digits that are not digits, a character that is not one scalar,
    ///   a width or a pattern no width literal has, and labels not strictly
    ///   increasing.
    /// - panics: none.
    /// - executable: none — the tag table is its own specification.
    ///
    /// # Errors
    /// [`ValueError`]: as listed above.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every head and literal kind round-trips; L3 — each
    ///   malformed payload kind is refused at its open record.
    /// - witness: `tests::crossing::every_crossing_head_commits_and_derefs_back_equal`
    /// - witness: `tests::crossing::a_payload_the_codec_does_not_write_refuses_its_constructor`
    fn read(reader: &mut TokenReader<'_>) -> Result<Node<'static>, ValueError>
    {
        let opened = Self {
            at: reader.position(),
            tag: reader.read_tag()?,
        };
        let crossed = match u8::from(opened.tag) {
            INTEGER | TEXT | NUMERIC | CHARACTER | FLOAT | FIXED => {
                return Ok(Node::Literal(Cow::Owned(opened.literal(reader)?)));
            },
            TUPLE => Crossed::Tuple(ProducerArity::from(opened.count(reader)?.0)),
            RECORD => Crossed::Record(opened.labels(reader)?),
            NIL => Crossed::Nil,
            CONS => Crossed::Cons,
            INJECTION => Crossed::Injection(Summand::from(opened.count(reader)?.0)),
            LIFT => Crossed::Lift(Cow::Owned(opened.level(reader)?)),
            DATA | FAMILY_DATA => {
                let tag = gandr_kernel_term::ConstructorTag::from(opened.count(reader)?.0);
                let arity = ProducerArity::from(opened.count(reader)?.0);
                let family = if u8::from(opened.tag) == FAMILY_DATA {
                    Some(ConstantIndex::from(opened.count(reader)?.0))
                }
                else {
                    None
                };
                Crossed::Data { tag, arity, family }
            },
            _ => return Err(opened.refused()),
        };
        Ok(Node::Constructed(crossed))
    }

    /// The refusal of this constructor: its tag or its payload is not one the
    /// codec writes.
    ///
    /// # Specification
    /// trivial.
    const fn refused(self) -> ValueError
    {
        ValueError::UnexpectedConstructor {
            found: self.tag,
            position: self.at,
        }
    }

    /// Read a literal's payload.
    ///
    /// # Specification
    /// - requires: the tag names a literal kind.
    /// - ensures: on success the literal its payload names, built by its kind's
    ///   constructor.
    /// - fails: as [`Opened::read`].
    /// - panics: none.
    /// - executable: none — as [`Opened::read`].
    ///
    /// # Errors
    /// [`ValueError`]: as [`Opened::read`].
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every literal kind reads back as written; L3 — a
    ///   malformed literal payload is refused at its open record.
    /// - witness: `tests::crossing::every_crossing_head_commits_and_derefs_back_equal`
    /// - witness: `tests::crossing::a_payload_the_codec_does_not_write_refuses_its_constructor`
    fn literal(
        self,
        reader: &mut TokenReader<'_>,
    ) -> Result<Literal, ValueError>
    {
        Ok(match u8::from(self.tag) {
            INTEGER => {
                let sign = self.sign(reader)?;
                Literal::Integer(IntegerLiteral::new(sign, self.magnitude(reader)?))
            },
            TEXT => Literal::Text(StringLiteral::new(self.text(reader)?)),
            NUMERIC => {
                let sign = self.sign(reader)?;
                let integral = self.magnitude(reader)?;
                let fraction = FractionDigits::from_decimal_text(self.text(reader)?)
                    .ok_or_else(|| self.refused())?;
                Literal::Numeric(NumericLiteral::new(sign, integral, fraction))
            },
            CHARACTER => {
                let scalar = u32::try_from(u64::from(reader.read_word()?))
                    .ok()
                    .and_then(char::from_u32)
                    .ok_or_else(|| self.refused())?;
                Literal::Character(CharacterLiteral::from(scalar))
            },
            FLOAT => Literal::Float64(Float64Literal::from(f64::from_bits(u64::from(
                reader.read_word()?,
            )))),
            FIXED => {
                let width = match u64::from(reader.read_word()?) {
                    0_u64 => IntegerWidth::U32,
                    1_u64 => IntegerWidth::U64,
                    2_u64 => IntegerWidth::I32,
                    3_u64 => IntegerWidth::I64,
                    _ => return Err(self.refused()),
                };
                let bits = u64::from(reader.read_word()?);
                Literal::Fixed(
                    FixedInteger::try_from((width, bits)).map_err(|_wider| self.refused())?,
                )
            },
            _ => return Err(self.refused()),
        })
    }

    /// Read a count or an ordinal.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// The reader's refusal, and this constructor's for a word wider than the
    /// host's counts.
    fn count(
        self,
        reader: &mut TokenReader<'_>,
    ) -> Result<Count, ValueError>
    {
        usize::try_from(u64::from(reader.read_word()?))
            .map(Count)
            .map_err(|_wider| self.refused())
    }

    /// Read a sign.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// The reader's refusal, and this constructor's for a word other than
    /// zero or one.
    fn sign(
        self,
        reader: &mut TokenReader<'_>,
    ) -> Result<Sign, ValueError>
    {
        match u64::from(reader.read_word()?) {
            0_u64 => Ok(Sign::NonNegative),
            1_u64 => Ok(Sign::Negative),
            _ => Err(self.refused()),
        }
    }

    /// Read UTF-8 text.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// The reader's refusal, and this constructor's for bytes that are not
    /// UTF-8.
    fn text(
        self,
        reader: &mut TokenReader<'_>,
    ) -> Result<String, ValueError>
    {
        let bytes = <&[u8]>::from(reader.read_bytes()?);
        core::str::from_utf8(bytes)
            .map(String::from)
            .map_err(|_not_text| self.refused())
    }

    /// Read decimal digits.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// As [`Opened::text`], and this constructor's for text that is not
    /// digits.
    fn magnitude(
        self,
        reader: &mut TokenReader<'_>,
    ) -> Result<Magnitude, ValueError>
    {
        Magnitude::from_decimal_text(self.text(reader)?).ok_or_else(|| self.refused())
    }

    /// Read a record's labels, refusing any not after the one before.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// As [`Opened::text`], and this constructor's for a label not strictly
    /// after the one before it as UTF-8 bytes.
    fn labels(
        self,
        reader: &mut TokenReader<'_>,
    ) -> Result<Arc<[FieldLabel]>, ValueError>
    {
        let count = self.count(reader)?.0;
        let mut labels: Vec<FieldLabel> = Vec::new();
        for _label in 0_usize .. count {
            let label = self.text(reader)?;
            if labels
                .last()
                .is_some_and(|before| before.as_ref().as_bytes() >= label.as_bytes())
            {
                return Err(self.refused());
            }
            labels.push(FieldLabel::from(label));
        }
        Ok(Arc::from(labels))
    }

    /// Read a level: its constant, then each atom's variable and offset.
    ///
    /// # Specification
    /// - requires: the reader stands at a lift's payload.
    /// - ensures: on success the join of the constant and each atom, its offset
    ///   built by successors as the kernel's decoder builds one.
    /// - fails: the reader's refusal, and this constructor's for a variable
    ///   wider than a level variable's index or an offset past the level's
    ///   ceiling.
    /// - panics: none.
    /// - executable: none — the join is the level algebra's.
    ///
    /// # Errors
    /// [`ValueError`]: as listed above.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a lift at a constant level and at a join of two atoms
    ///   round-trips.
    /// - witness: `tests::crossing::every_crossing_head_commits_and_derefs_back_equal`
    fn level(
        self,
        reader: &mut TokenReader<'_>,
    ) -> Result<Level, ValueError>
    {
        let constant = LevelConstant::from(u64::from(reader.read_word()?));
        let atoms = self.count(reader)?.0;
        let mut level = Level::constant(constant);
        for _atom in 0_usize .. atoms {
            let variable =
                u32::try_from(u64::from(reader.read_word()?)).map_err(|_wider| self.refused())?;
            let mut atom = Level::var(LevelVar::new(LevelVarIndex::from(variable)));
            for _successor in 0_u64 .. u64::from(reader.read_word()?) {
                atom = atom.succ().map_err(|_past| self.refused())?;
            }
            level = level.max(&atom);
        }
        Ok(level)
    }
}
