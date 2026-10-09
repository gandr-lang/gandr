//! The canonical byte form: one encoding for item identities, program
//! addresses and persisted checkpoint sets.
//!
//! # One writer, two sinks
//!
//! Every value is written by one set of functions into a [`Sink`]: a byte
//! buffer when the bytes are kept, a BLAKE3 hasher when only their digest is.
//! An item's identity digest is therefore the digest of exactly the bytes its
//! checkpoint would persist, and computing it allocates nothing.
//!
//! # Decoding refuses what encoding would not write
//!
//! The reader checks structure as it goes — tags, lengths, child indices and
//! their sorts — and a decoded value is written again and compared with its
//! input, so a payload that parses but is not the one canonical spelling of
//! its value is refused rather than accepted under a second address. A table
//! is also checked to be numbered by discovery from its roots, which writing
//! it again would not reveal. Counts read from the input never size an
//! allocation: a corrupted count fails at the end of the input instead.

use alloc::collections::BTreeSet;
use alloc::string::String;
use alloc::vec::Vec;
use core::fmt;

use gandr_core_checker::CheckBudget;
use gandr_core_checker::ConversionCount;
use gandr_core_checker::ExpectedShape;
use gandr_core_checker::UnadmittedFormer;
use gandr_core_checker::body;
use gandr_core_checker::signature;
use gandr_core_term::BinderDepth;
use gandr_core_term::Sort as TypeSort;
use gandr_core_term::SortParameter;
use gandr_core_term::Zone;
use gandr_kernel_strata::Level;
use gandr_kernel_strata::LevelConstant;
use gandr_kernel_strata::LevelOffset;
use gandr_kernel_strata::LevelVar;
use gandr_kernel_strata::LevelVarIndex;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::FractionDigits;
use gandr_kernel_term::GroundSort;
use gandr_kernel_term::IntegerLiteral;
use gandr_kernel_term::Literal;
use gandr_kernel_term::Magnitude;
use gandr_kernel_term::NumericLiteral;
use gandr_kernel_term::Side;
use gandr_kernel_term::Sign;
use gandr_kernel_term::StringLiteral;
use quenchant_shape::shape::Maybe;

use crate::boundary::NodeIndex;
use crate::boundary::Occurrence;
use crate::checkpoint::Answer;
use crate::checkpoint::Answered;
use crate::checkpoint::Checkpoints;
use crate::checkpoint::ItemCheckpoint;
use crate::content::ContentNode;
use crate::content::ItemContent;
use crate::content::Opacity;
use crate::content::Sort;
use crate::content::TypeContent;
use crate::footprint::Footprint;
use crate::footprint::HoleMark;
use crate::region::ItemKey;
use crate::region::Reference;
use crate::typing::Form;
use crate::typing::Refusal;
use crate::typing::Site;
use crate::typing::Typing;

/// The magic and version a persisted checkpoint set opens with.
const CHECKPOINTS_MAGIC: &[u8; 8] = b"GCKPT\0\0\x02";
/// The magic and version a program's address is computed over.
const PROGRAM_MAGIC: &[u8; 8] = b"GPROG\0\0\x01";
/// The decoder's cap on a level atom's offset.
///
/// A level holds `x + o` only as `o` successors of `x`, so decoding an offset
/// costs `o` steps; the cap keeps a corrupted offset from costing more than a
/// bounded loop. No type the checker forms comes near it.
pub const MAX_DECODED_LEVEL_OFFSET: u64 = 4096;

/// A form the persistent encoding has no spelling for.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum UnsupportedPersistence
{
    /// An id of this sort that the item's arena resolves to nothing: a fact
    /// about another arena, meaningless outside this process.
    Dangling(Sort),
}

/// Why bytes are not a canonical encoding, or a value has none.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum CodecError
{
    /// The bytes are truncated, carry trailing bytes, or break the grammar.
    Corrupt,
    /// The bytes parse, but are not the one canonical spelling of their value.
    NonCanonical,
    /// A level atom's offset meets the decoder's cap.
    LevelOffsetTooLarge
    {
        /// The offset read.
        offset: LevelOffset,
    },
    /// The value holds a form the encoding has no spelling for.
    Unsupported(UnsupportedPersistence),
    /// A length does not fit the encoding's width.
    Unrepresentable,
}

impl fmt::Display for UnsupportedPersistence
{
    /// Writes the form's name.
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
            | Self::Dangling(sort) => {
                let sort = match sort {
                    | Sort::Value => "value",
                    | Sort::Computation => "computation",
                    | Sort::ValueType => "value type",
                    | Sort::CompType => "computation type",
                };
                write!(f, "an unresolved {sort} id is process-local")
            },
        }
    }
}

/// A borrowed run of bytes.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Bytes<'data>(pub &'data [u8]);

/// The canonical bytes of a checkpoint set.
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, Hash, PartialEq)]
pub struct CheckpointBytes(Vec<u8>);

impl From<Vec<u8>> for CheckpointBytes
{
    /// Wraps bytes read from elsewhere, to be decoded.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(bytes: Vec<u8>) -> Self
    {
        Self(bytes)
    }
}

impl From<CheckpointBytes> for Vec<u8>
{
    /// Unwraps the bytes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(bytes: CheckpointBytes) -> Self
    {
        bytes.0
    }
}

impl AsRef<[u8]> for CheckpointBytes
{
    /// Borrows the bytes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &[u8]
    {
        &self.0
    }
}

/// One byte naming a variant.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Tag(u8);

/// A little-endian 64-bit word.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Word(u64);

/// A length or a count.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Count(usize);

/// Where encoded bytes go.
pub trait Sink
{
    /// Append `bytes`.
    ///
    /// # Specification
    /// trivial.
    fn put(
        &mut self,
        bytes: Bytes<'_>,
    );
}

impl Sink for CheckpointBytes
{
    /// Append to the buffer.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn put(
        &mut self,
        bytes: Bytes<'_>,
    )
    {
        self.0.extend_from_slice(bytes.0);
    }
}

impl Sink for blake3::Hasher
{
    /// Feed the hasher.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn put(
        &mut self,
        bytes: Bytes<'_>,
    )
    {
        let _hasher = self.update(bytes.0);
    }
}

/// The primitive writes, over one sink.
#[repr(transparent)]
struct Writer<'sink, Out>
{
    /// The sink written to.
    sink: &'sink mut Out,
}

impl<Out> Writer<'_, Out>
where
    Out: Sink,
{
    /// Write one tag byte.
    ///
    /// # Specification
    /// trivial.
    fn tag(
        &mut self,
        tag: Tag,
    )
    {
        self.sink.put(Bytes(&[tag.0]));
    }

    /// Write one word.
    ///
    /// # Specification
    /// trivial.
    fn word(
        &mut self,
        word: Word,
    )
    {
        self.sink.put(Bytes(&word.0.to_le_bytes()));
    }

    /// Write one count as a word.
    ///
    /// # Specification
    /// - fails: [`CodecError::Unrepresentable`] when the count passes 64 bits.
    /// - panics: none.
    fn count(
        &mut self,
        count: Count,
    ) -> Result<(), CodecError>
    {
        let word = u64::try_from(count.0).map_err(|_overflow| CodecError::Unrepresentable)?;
        self.word(Word(word));
        Ok(())
    }

    /// Write a length-prefixed run of bytes.
    ///
    /// # Specification
    /// - fails: as [`Self::count`].
    /// - panics: none.
    fn bytes(
        &mut self,
        bytes: Bytes<'_>,
    ) -> Result<(), CodecError>
    {
        self.count(Count(bytes.0.len()))?;
        self.sink.put(bytes);
        Ok(())
    }
}

/// The primitive reads, over one input.
struct Reader<'data>
{
    /// The input.
    bytes: &'data [u8],
    /// The next unread byte.
    cursor: usize,
}

impl<'data> Reader<'data>
{
    /// Read the next `count` bytes.
    ///
    /// # Specification
    /// - fails: [`CodecError::Corrupt`] past the end of the input.
    /// - panics: none.
    fn take(
        &mut self,
        count: Count,
    ) -> Result<Bytes<'data>, CodecError>
    {
        let end = self
            .cursor
            .checked_add(count.0)
            .ok_or(CodecError::Corrupt)?;
        let taken = self
            .bytes
            .get(self.cursor .. end)
            .ok_or(CodecError::Corrupt)?;
        self.cursor = end;
        Ok(Bytes(taken))
    }

    /// Read one tag byte.
    ///
    /// # Specification
    /// trivial.
    fn tag(&mut self) -> Result<Tag, CodecError>
    {
        let taken = self.take(Count(1))?;
        match *taken.0 {
            | [tag] => Ok(Tag(tag)),
            | _ => Err(CodecError::Corrupt),
        }
    }

    /// Read one word.
    ///
    /// # Specification
    /// trivial.
    fn word(&mut self) -> Result<Word, CodecError>
    {
        let taken = self.take(Count(8))?;
        let array: [u8; 8] = taken.0.try_into().map_err(|_short| CodecError::Corrupt)?;
        Ok(Word(u64::from_le_bytes(array)))
    }

    /// Read one count.
    ///
    /// # Specification
    /// trivial.
    fn count(&mut self) -> Result<Count, CodecError>
    {
        let word = self.word()?;
        let count = usize::try_from(word.0).map_err(|_overflow| CodecError::Corrupt)?;
        Ok(Count(count))
    }

    /// Read a length-prefixed run of bytes.
    ///
    /// # Specification
    /// trivial.
    fn bytes(&mut self) -> Result<Bytes<'data>, CodecError>
    {
        let count = self.count()?;
        self.take(count)
    }

    /// Read a length-prefixed run of UTF-8 text.
    ///
    /// # Specification
    /// trivial.
    fn text(&mut self) -> Result<String, CodecError>
    {
        let bytes = self.bytes()?;
        String::from_utf8(bytes.0.to_vec()).map_err(|_invalid| CodecError::Corrupt)
    }

    /// Require that the whole input was read.
    ///
    /// # Specification
    /// - fails: [`CodecError::Corrupt`] when bytes remain.
    /// - panics: none.
    fn finish(&self) -> Result<(), CodecError>
    {
        if self.cursor == self.bytes.len() {
            Ok(())
        }
        else {
            Err(CodecError::Corrupt)
        }
    }
}

/// A count as a word, for fields the vocabulary types as `usize`.
///
/// # Specification
/// trivial.
fn word_of(count: Count) -> Result<Word, CodecError>
{
    let word = u64::try_from(count.0).map_err(|_overflow| CodecError::Unrepresentable)?;
    Ok(Word(word))
}

/// Write a reference.
///
/// # Specification
/// trivial.
fn write_reference<Out>(
    writer: &mut Writer<'_, Out>,
    reference: &Reference,
) -> Result<(), CodecError>
where
    Out: Sink,
{
    match *reference {
        | Reference::Unoccupied => writer.tag(Tag(0)),
        | Reference::Item {
            ref key,
            occurrence,
        } => {
            writer.tag(Tag(1));
            writer.bytes(Bytes(key.as_ref()))?;
            writer.count(Count(usize::from(occurrence)))?;
        },
    }
    Ok(())
}

/// The canonical bytes of one reference, for tests that rewrite a payload.
///
/// # Specification
/// trivial.
#[cfg(test)]
pub fn reference_bytes(reference: &Reference) -> CheckpointBytes
{
    let mut bytes = CheckpointBytes::default();
    let mut writer = Writer { sink: &mut bytes };
    write_reference(&mut writer, reference).expect("a reference always encodes");
    bytes
}

/// Read a reference.
///
/// # Specification
/// trivial.
fn read_reference(reader: &mut Reader<'_>) -> Result<Reference, CodecError>
{
    let tag = reader.tag()?;
    match tag.0 {
        | 0 => Ok(Reference::Unoccupied),
        | 1 => {
            let key = reader.bytes()?;
            let occurrence = reader.count()?;
            Ok(Reference::Item {
                key: ItemKey::from(key.0),
                occurrence: Occurrence::from(occurrence.0),
            })
        },
        | _ => Err(CodecError::Corrupt),
    }
}

/// Write a level: its constant, then its atoms ascending.
///
/// # Specification
/// trivial.
fn write_level<Out>(
    writer: &mut Writer<'_, Out>,
    level: &Level,
) -> Result<(), CodecError>
where
    Out: Sink,
{
    writer.word(Word(u64::from(level.constant_part())));
    writer.count(Count(level.atoms().count()))?;
    for (variable, offset) in level.atoms() {
        writer.word(Word(u64::from(u32::from(variable.index()))));
        writer.word(Word(u64::from(offset)));
    }
    Ok(())
}

/// Read a level, refusing an offset at or past the cap.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the level `max(c, x₁ + o₁, …)` the bytes spell.
/// - fails: [`CodecError::LevelOffsetTooLarge`] naming the first offset at or
///   past [`MAX_DECODED_LEVEL_OFFSET`]; [`CodecError::Corrupt`] for a malformed
///   level.
/// - panics: none.
/// - intension: an atom of offset `o` costs `o` successor steps, bounded by the
///   cap.
///
/// # Adequacy
/// - hypothesis: L3 — the surface is the cap, separated by an atom whose offset
///   sits exactly at the cap, refused with exactly that offset, beside one just
///   under it that round trips.
/// - witness: `persistence::tests::oversized_level_offset_is_refused_with_exact_error`
fn read_level(reader: &mut Reader<'_>) -> Result<Level, CodecError>
{
    let constant = reader.word()?;
    let atoms = reader.count()?;
    let mut level = Level::constant(LevelConstant::from(constant.0));
    for _ in 0 .. atoms.0 {
        let variable = reader.word()?;
        let variable = u32::try_from(variable.0).map_err(|_overflow| CodecError::Corrupt)?;
        let offset = reader.word()?;
        if offset.0 >= MAX_DECODED_LEVEL_OFFSET {
            return Err(CodecError::LevelOffsetTooLarge {
                offset: LevelOffset::from(offset.0),
            });
        }
        let mut atom = Level::var(LevelVar::new(LevelVarIndex::from(variable)));
        for _ in 0 .. offset.0 {
            atom = atom.succ().map_err(|_overflow| CodecError::Corrupt)?;
        }
        level = level.max(&atom);
    }
    Ok(level)
}

/// The tag of a sign.
///
/// # Specification
/// trivial.
const fn sign_tag(sign: Sign) -> Tag
{
    match sign {
        | Sign::Negative => Tag(0),
        | Sign::NonNegative => Tag(1),
    }
}

/// Read a sign.
///
/// # Specification
/// trivial.
fn read_sign(reader: &mut Reader<'_>) -> Result<Sign, CodecError>
{
    let tag = reader.tag()?;
    match tag.0 {
        | 0 => Ok(Sign::Negative),
        | 1 => Ok(Sign::NonNegative),
        | _ => Err(CodecError::Corrupt),
    }
}

/// Write a literal.
///
/// # Specification
/// trivial.
fn write_literal<Out>(
    writer: &mut Writer<'_, Out>,
    literal: &Literal,
) -> Result<(), CodecError>
where
    Out: Sink,
{
    match *literal {
        | Literal::Integer(ref integer) => {
            writer.tag(Tag(0));
            writer.tag(sign_tag(integer.sign()));
            writer.bytes(Bytes(integer.magnitude().as_ref().as_bytes()))?;
        },
        | Literal::Text(ref string) => {
            writer.tag(Tag(1));
            writer.bytes(Bytes(string.as_ref().as_bytes()))?;
        },
        | Literal::Numeric(ref numeric) => {
            writer.tag(Tag(2));
            writer.tag(sign_tag(numeric.sign()));
            writer.bytes(Bytes(numeric.integer_part().as_ref().as_bytes()))?;
            writer.bytes(Bytes(numeric.fraction().as_ref().as_bytes()))?;
        },
    }
    Ok(())
}

/// Read a literal.
///
/// # Specification
/// trivial.
fn read_literal(reader: &mut Reader<'_>) -> Result<Literal, CodecError>
{
    let tag = reader.tag()?;
    match tag.0 {
        | 0 => {
            let sign = read_sign(reader)?;
            let digits = reader.text()?;
            let magnitude = Magnitude::from_decimal_text(digits).ok_or(CodecError::Corrupt)?;
            Ok(Literal::Integer(IntegerLiteral::new(sign, magnitude)))
        },
        | 1 => {
            let text = reader.text()?;
            Ok(Literal::Text(StringLiteral::new(text)))
        },
        | 2 => {
            let sign = read_sign(reader)?;
            let digits = reader.text()?;
            let integer_part = Magnitude::from_decimal_text(digits).ok_or(CodecError::Corrupt)?;
            let digits = reader.text()?;
            let fraction = FractionDigits::from_decimal_text(digits).ok_or(CodecError::Corrupt)?;
            Ok(Literal::Numeric(NumericLiteral::new(
                sign,
                integer_part,
                fraction,
            )))
        },
        | _ => Err(CodecError::Corrupt),
    }
}

/// Write a node index.
///
/// # Specification
/// trivial.
fn write_index<Out>(
    writer: &mut Writer<'_, Out>,
    index: NodeIndex,
) -> Result<(), CodecError>
where
    Out: Sink,
{
    writer.count(Count(usize::from(index)))
}

/// Read a node index.
///
/// # Specification
/// trivial.
fn read_index(reader: &mut Reader<'_>) -> Result<NodeIndex, CodecError>
{
    let count = reader.count()?;
    Ok(NodeIndex::from(count.0))
}

/// Write one content node.
///
/// # Specification
/// - fails: [`CodecError::Unsupported`] for an unresolved node.
/// - panics: none.
fn write_node<Out>(
    writer: &mut Writer<'_, Out>,
    node: &ContentNode,
) -> Result<(), CodecError>
where
    Out: Sink,
{
    match *node {
        | ContentNode::Variable { zone, index } => {
            writer.tag(Tag(0x01));
            writer.tag(match zone {
                | Zone::Intuitionistic => Tag(0),
                | Zone::Linear => Tag(1),
            });
            writer.word(Word(u64::from(u32::from(index))));
        },
        | ContentNode::Constant(ref reference) => {
            writer.tag(Tag(0x02));
            write_reference(writer, reference)?;
        },
        | ContentNode::Unit => writer.tag(Tag(0x03)),
        | ContentNode::Literal(ref literal) => {
            writer.tag(Tag(0x04));
            write_literal(writer, literal)?;
        },
        | ContentNode::Pair(first, second) => {
            writer.tag(Tag(0x05));
            write_index(writer, first)?;
            write_index(writer, second)?;
        },
        | ContentNode::Injection(side, body) => {
            writer.tag(Tag(0x06));
            writer.tag(match side {
                | Side::Left => Tag(0),
                | Side::Right => Tag(1),
            });
            write_index(writer, body)?;
        },
        | ContentNode::Thunk(body) => {
            writer.tag(Tag(0x07));
            write_index(writer, body)?;
        },
        | ContentNode::ValueLift { ref target, body } => {
            writer.tag(Tag(0x08));
            write_level(writer, target)?;
            write_index(writer, body)?;
        },
        | ContentNode::Quote(quoted) => {
            writer.tag(Tag(0x09));
            write_index(writer, quoted)?;
        },
        | ContentNode::QuoteComputation(quoted) => {
            writer.tag(Tag(0x0A));
            write_index(writer, quoted)?;
        },
        | ContentNode::StaticLambda(body) => {
            writer.tag(Tag(0x0B));
            write_index(writer, body)?;
        },
        | ContentNode::StaticApplication(head, argument) => {
            writer.tag(Tag(0x0C));
            write_index(writer, head)?;
            write_index(writer, argument)?;
        },
        | ContentNode::Lambda(body) => {
            writer.tag(Tag(0x10));
            write_index(writer, body)?;
        },
        | ContentNode::Application(head, argument) => {
            writer.tag(Tag(0x11));
            write_index(writer, head)?;
            write_index(writer, argument)?;
        },
        | ContentNode::Return(value) => {
            writer.tag(Tag(0x12));
            write_index(writer, value)?;
        },
        | ContentNode::Bind(bound, rest) => {
            writer.tag(Tag(0x13));
            write_index(writer, bound)?;
            write_index(writer, rest)?;
        },
        | ContentNode::Force(value) => {
            writer.tag(Tag(0x14));
            write_index(writer, value)?;
        },
        | ContentNode::Case {
            scrutinee,
            on_left,
            on_right,
        } => {
            writer.tag(Tag(0x15));
            write_index(writer, scrutinee)?;
            write_index(writer, on_left)?;
            write_index(writer, on_right)?;
        },
        | ContentNode::Base(base) => {
            writer.tag(Tag(0x20));
            writer.tag(match base {
                | BaseType::Integer => Tag(0),
                | BaseType::String => Tag(1),
                | BaseType::Numeric => Tag(2),
            });
        },
        | ContentNode::UnitType => writer.tag(Tag(0x21)),
        | ContentNode::Product(first, second) => {
            writer.tag(Tag(0x22));
            write_index(writer, first)?;
            write_index(writer, second)?;
        },
        | ContentNode::Sum(first, second) => {
            writer.tag(Tag(0x23));
            write_index(writer, first)?;
            write_index(writer, second)?;
        },
        | ContentNode::ThunkType(body) => {
            writer.tag(Tag(0x24));
            write_index(writer, body)?;
        },
        // The value universe keeps the tag it had before the sorts were
        // spelled, and the other two sorts take fresh tags, so a table
        // written before the families reads the same after them.
        | ContentNode::Universe {
            sort: TypeSort::Ground(GroundSort::Value),
            ref level,
        } => {
            writer.tag(Tag(0x25));
            write_level(writer, level)?;
        },
        | ContentNode::Universe {
            sort: TypeSort::Ground(GroundSort::Computation),
            ref level,
        } => {
            writer.tag(Tag(0x29));
            write_level(writer, level)?;
        },
        | ContentNode::Universe {
            sort: TypeSort::Parameter(parameter),
            ref level,
        } => {
            writer.tag(Tag(0x2A));
            writer.word(Word(u64::from(u32::from(parameter))));
            write_level(writer, level)?;
        },
        | ContentNode::TypeLift { inner, ref target } => {
            writer.tag(Tag(0x26));
            write_index(writer, inner)?;
            write_level(writer, target)?;
        },
        | ContentNode::Element { code, ref target } => {
            writer.tag(Tag(0x27));
            write_index(writer, code)?;
            write_level(writer, target)?;
        },
        | ContentNode::Abstract(ref reference) => {
            writer.tag(Tag(0x28));
            write_reference(writer, reference)?;
        },
        | ContentNode::StaticPi { domain, codomain } => {
            writer.tag(Tag(0x2B));
            write_index(writer, domain)?;
            write_index(writer, codomain)?;
        },
        | ContentNode::Returner(result) => {
            writer.tag(Tag(0x30));
            write_index(writer, result)?;
        },
        | ContentNode::Arrow { domain, codomain } => {
            writer.tag(Tag(0x31));
            write_index(writer, domain)?;
            write_index(writer, codomain)?;
        },
        | ContentNode::Pi { domain, codomain } => {
            writer.tag(Tag(0x32));
            write_index(writer, domain)?;
            write_index(writer, codomain)?;
        },
        | ContentNode::ComputationElement { code, ref target } => {
            writer.tag(Tag(0x33));
            write_index(writer, code)?;
            write_level(writer, target)?;
        },
        | ContentNode::Unresolved(sort) => {
            return Err(CodecError::Unsupported(UnsupportedPersistence::Dangling(
                sort,
            )));
        },
    }
    Ok(())
}

/// Read one content node.
///
/// # Specification
/// - fails: [`CodecError::Corrupt`] for an unknown tag or a malformed field; no
///   tag spells an unresolved node.
/// - panics: none.
fn read_node(reader: &mut Reader<'_>) -> Result<ContentNode, CodecError>
{
    let tag = reader.tag()?;
    let node = match tag.0 {
        | 0x01 => {
            let zone = reader.tag()?;
            let zone = match zone.0 {
                | 0 => Zone::Intuitionistic,
                | 1 => Zone::Linear,
                | _ => return Err(CodecError::Corrupt),
            };
            let index = reader.word()?;
            let index = u32::try_from(index.0).map_err(|_overflow| CodecError::Corrupt)?;
            ContentNode::Variable {
                zone,
                index: DeBruijnIndex::from(index),
            }
        },
        | 0x02 => {
            let reference = read_reference(reader)?;
            ContentNode::Constant(reference)
        },
        | 0x03 => ContentNode::Unit,
        | 0x04 => {
            let literal = read_literal(reader)?;
            ContentNode::Literal(literal)
        },
        | 0x05 => {
            let first = read_index(reader)?;
            let second = read_index(reader)?;
            ContentNode::Pair(first, second)
        },
        | 0x06 => {
            let side = reader.tag()?;
            let side = match side.0 {
                | 0 => Side::Left,
                | 1 => Side::Right,
                | _ => return Err(CodecError::Corrupt),
            };
            let body = read_index(reader)?;
            ContentNode::Injection(side, body)
        },
        | 0x07 => {
            let body = read_index(reader)?;
            ContentNode::Thunk(body)
        },
        | 0x08 => {
            let target = read_level(reader)?;
            let body = read_index(reader)?;
            ContentNode::ValueLift { target, body }
        },
        | 0x09 => {
            let quoted = read_index(reader)?;
            ContentNode::Quote(quoted)
        },
        | 0x0A => {
            let quoted = read_index(reader)?;
            ContentNode::QuoteComputation(quoted)
        },
        | 0x0B => {
            let body = read_index(reader)?;
            ContentNode::StaticLambda(body)
        },
        | 0x0C => {
            let head = read_index(reader)?;
            let argument = read_index(reader)?;
            ContentNode::StaticApplication(head, argument)
        },
        | 0x10 => {
            let body = read_index(reader)?;
            ContentNode::Lambda(body)
        },
        | 0x11 => {
            let head = read_index(reader)?;
            let argument = read_index(reader)?;
            ContentNode::Application(head, argument)
        },
        | 0x12 => {
            let value = read_index(reader)?;
            ContentNode::Return(value)
        },
        | 0x13 => {
            let bound = read_index(reader)?;
            let rest = read_index(reader)?;
            ContentNode::Bind(bound, rest)
        },
        | 0x14 => {
            let value = read_index(reader)?;
            ContentNode::Force(value)
        },
        | 0x15 => {
            let scrutinee = read_index(reader)?;
            let on_left = read_index(reader)?;
            let on_right = read_index(reader)?;
            ContentNode::Case {
                scrutinee,
                on_left,
                on_right,
            }
        },
        | 0x20 => {
            let base = reader.tag()?;
            ContentNode::Base(match base.0 {
                | 0 => BaseType::Integer,
                | 1 => BaseType::String,
                | 2 => BaseType::Numeric,
                | _ => return Err(CodecError::Corrupt),
            })
        },
        | 0x21 => ContentNode::UnitType,
        | 0x22 => {
            let first = read_index(reader)?;
            let second = read_index(reader)?;
            ContentNode::Product(first, second)
        },
        | 0x23 => {
            let first = read_index(reader)?;
            let second = read_index(reader)?;
            ContentNode::Sum(first, second)
        },
        | 0x24 => {
            let body = read_index(reader)?;
            ContentNode::ThunkType(body)
        },
        | 0x25 => {
            let level = read_level(reader)?;
            ContentNode::Universe {
                sort: TypeSort::Ground(GroundSort::Value),
                level,
            }
        },
        | 0x26 => {
            let inner = read_index(reader)?;
            let target = read_level(reader)?;
            ContentNode::TypeLift { inner, target }
        },
        | 0x27 => {
            let code = read_index(reader)?;
            let target = read_level(reader)?;
            ContentNode::Element { code, target }
        },
        | 0x28 => {
            let reference = read_reference(reader)?;
            ContentNode::Abstract(reference)
        },
        | 0x29 => {
            let level = read_level(reader)?;
            ContentNode::Universe {
                sort: TypeSort::Ground(GroundSort::Computation),
                level,
            }
        },
        | 0x2A => {
            let parameter = reader.word()?;
            let parameter = u32::try_from(parameter.0).map_err(|_overflow| CodecError::Corrupt)?;
            let level = read_level(reader)?;
            ContentNode::Universe {
                sort: TypeSort::Parameter(SortParameter::from(parameter)),
                level,
            }
        },
        | 0x2B => {
            let domain = read_index(reader)?;
            let codomain = read_index(reader)?;
            ContentNode::StaticPi { domain, codomain }
        },
        | 0x30 => {
            let result = read_index(reader)?;
            ContentNode::Returner(result)
        },
        | 0x31 => {
            let domain = read_index(reader)?;
            let codomain = read_index(reader)?;
            ContentNode::Arrow { domain, codomain }
        },
        | 0x32 => {
            let domain = read_index(reader)?;
            let codomain = read_index(reader)?;
            ContentNode::Pi { domain, codomain }
        },
        | 0x33 => {
            let code = read_index(reader)?;
            let target = read_level(reader)?;
            ContentNode::ComputationElement { code, target }
        },
        | _ => return Err(CodecError::Corrupt),
    };
    Ok(node)
}

/// Write a table.
///
/// # Specification
/// trivial.
fn write_nodes<Out>(
    writer: &mut Writer<'_, Out>,
    nodes: &[ContentNode],
) -> Result<(), CodecError>
where
    Out: Sink,
{
    writer.count(Count(nodes.len()))?;
    for node in nodes {
        write_node(writer, node)?;
    }
    Ok(())
}

/// Read a table and check it is numbered by discovery from `roots`, every
/// child in range and of the sort its former requires.
///
/// # Specification
/// - requires: nothing.
/// - ensures: on success a table every index of which is reached, in discovery
///   order, from the roots the caller then reads.
/// - fails: [`CodecError::Corrupt`] for a child out of range or of the wrong
///   sort; [`CodecError::NonCanonical`] for a table not numbered by discovery,
///   or holding a node no root reaches.
/// - panics: none.
fn read_nodes(reader: &mut Reader<'_>) -> Result<Vec<ContentNode>, CodecError>
{
    let count = reader.count()?;
    let mut nodes = Vec::new();
    for _ in 0 .. count.0 {
        let node = read_node(reader)?;
        nodes.push(node);
    }
    for node in &nodes {
        for (child, sort) in node.children().iter() {
            match nodes.get(usize::from(child)) {
                | Some(found) if found.sort() == sort => {},
                | Some(_) | None => return Err(CodecError::Corrupt),
            }
        }
    }
    Ok(nodes)
}

/// Check that `nodes` is numbered by discovery from `roots`, in order.
///
/// # Specification
/// - requires: every child index of `nodes` is in range.
/// - ensures: `Ok` exactly when a breadth-first walk from the roots, children
///   left to right, discovers the indices `0, 1, …` in order and reaches them
///   all.
/// - fails: [`CodecError::NonCanonical`] otherwise; [`CodecError::Corrupt`] for
///   a root out of range.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the surfaces are the order and the reach, separated by a
///   table whose two entries are swapped and a table carrying an entry no root
///   reaches.
/// - witness: `persistence::tests::checkpoint_decoder_rejects_parseable_noncanonical_payload`
fn check_discovery(
    nodes: &[ContentNode],
    roots: &[NodeIndex],
) -> Result<(), CodecError>
{
    let mut seen = alloc::vec![false; nodes.len()];
    let mut next = 0_usize;
    let mut queue = alloc::collections::VecDeque::new();
    let mut discover = |index: NodeIndex,
                        queue: &mut alloc::collections::VecDeque<NodeIndex>|
     -> Result<(), CodecError> {
        let mark = seen
            .get_mut(usize::from(index))
            .ok_or(CodecError::Corrupt)?;
        if !*mark {
            if usize::from(index) != next {
                return Err(CodecError::NonCanonical);
            }
            *mark = true;
            next = next.saturating_add(1);
            queue.push_back(index);
        }
        Ok(())
    };
    for &root in roots {
        discover(root, &mut queue)?;
    }
    while let Some(index) = queue.pop_front() {
        let node = nodes.get(usize::from(index)).ok_or(CodecError::Corrupt)?;
        for (child, _) in node.children().iter() {
            discover(child, &mut queue)?;
        }
    }
    if next == nodes.len() {
        Ok(())
    }
    else {
        Err(CodecError::NonCanonical)
    }
}

/// Write an item's content.
///
/// # Specification
/// trivial.
pub fn write_item_content<Out>(
    sink: &mut Out,
    content: &ItemContent,
) -> Result<(), CodecError>
where
    Out: Sink,
{
    let mut writer = Writer { sink };
    write_item_content_with(&mut writer, content)
}

/// Write an item's content.
///
/// # Specification
/// trivial.
fn write_item_content_with<Out>(
    writer: &mut Writer<'_, Out>,
    content: &ItemContent,
) -> Result<(), CodecError>
where
    Out: Sink,
{
    write_reference(writer, content.reference())?;
    match content.signature() {
        | Maybe::Present(root) => {
            writer.tag(Tag(1));
            write_index(writer, root)?;
        },
        | Maybe::Absent(signature::Absent::Unsigned) => writer.tag(Tag(0)),
    }
    match content.body() {
        | Maybe::Present(root) => {
            writer.tag(Tag(1));
            write_index(writer, root)?;
        },
        | Maybe::Absent(body::Absent::Hole) => writer.tag(Tag(0)),
    }
    write_nodes(writer, content.nodes())
}

/// Read an item's content.
///
/// # Specification
/// - fails: as [`read_nodes`] and [`check_discovery`], and
///   [`CodecError::Corrupt`] for a signature root that is no value type or a
///   body root that is no value.
/// - panics: none.
fn read_item_content(reader: &mut Reader<'_>) -> Result<ItemContent, CodecError>
{
    let reference = read_reference(reader)?;
    let signed = reader.tag()?;
    let signature = match signed.0 {
        | 0 => Maybe::Absent(signature::Absent::Unsigned),
        | 1 => {
            let root = read_index(reader)?;
            Maybe::Present(root)
        },
        | _ => return Err(CodecError::Corrupt),
    };
    let bodied = reader.tag()?;
    let body = match bodied.0 {
        | 0 => Maybe::Absent(body::Absent::Hole),
        | 1 => {
            let root = read_index(reader)?;
            Maybe::Present(root)
        },
        | _ => return Err(CodecError::Corrupt),
    };
    let nodes = read_nodes(reader)?;
    let mut roots = Vec::with_capacity(2);
    if let Maybe::Present(root) = signature {
        root_of_sort(&nodes, root, Sort::ValueType)?;
        roots.push(root);
    }
    if let Maybe::Present(root) = body {
        root_of_sort(&nodes, root, Sort::Value)?;
        roots.push(root);
    }
    check_discovery(&nodes, &roots)?;
    Ok(ItemContent::from_parts(reference, signature, body, nodes))
}

/// Require that the root `root` of `nodes` has sort `sort`.
///
/// # Specification
/// trivial.
fn root_of_sort(
    nodes: &[ContentNode],
    root: NodeIndex,
    sort: Sort,
) -> Result<(), CodecError>
{
    match nodes.get(usize::from(root)) {
        | Some(node) if node.sort() == sort => Ok(()),
        | Some(_) | None => Err(CodecError::Corrupt),
    }
}

/// Write a type's content.
///
/// # Specification
/// trivial.
fn write_type<Out>(
    writer: &mut Writer<'_, Out>,
    content: &TypeContent,
) -> Result<(), CodecError>
where
    Out: Sink,
{
    write_nodes(writer, content.nodes())
}

/// Read a type's content.
///
/// # Specification
/// - fails: as [`read_nodes`] and [`check_discovery`], and
///   [`CodecError::Corrupt`] for an empty table or a root that is no type.
/// - panics: none.
fn read_type(reader: &mut Reader<'_>) -> Result<TypeContent, CodecError>
{
    let nodes = read_nodes(reader)?;
    match nodes.first().map(ContentNode::sort) {
        | Some(Sort::ValueType | Sort::CompType) => {},
        | Some(Sort::Value | Sort::Computation) | None => return Err(CodecError::Corrupt),
    }
    check_discovery(&nodes, &[NodeIndex::from(0_usize)])?;
    Ok(TypeContent::from_nodes(nodes))
}

/// Write a set of references, ascending.
///
/// # Specification
/// trivial.
fn write_references<'set, Out, References>(
    writer: &mut Writer<'_, Out>,
    references: References,
) -> Result<(), CodecError>
where
    Out: Sink,
    References: ExactSizeIterator<Item = &'set Reference>,
{
    writer.count(Count(references.len()))?;
    for reference in references {
        write_reference(writer, reference)?;
    }
    Ok(())
}

/// Read a set of references.
///
/// # Specification
/// trivial.
fn read_references(reader: &mut Reader<'_>) -> Result<BTreeSet<Reference>, CodecError>
{
    let count = reader.count()?;
    let mut references = BTreeSet::new();
    for _ in 0 .. count.0 {
        let reference = read_reference(reader)?;
        let _fresh = references.insert(reference);
    }
    Ok(references)
}

/// Write a footprint.
///
/// # Specification
/// trivial.
fn write_footprint<Out>(
    writer: &mut Writer<'_, Out>,
    footprint: &Footprint,
) -> Result<(), CodecError>
where
    Out: Sink,
{
    write_references(writer, footprint.reads())?;
    write_references(writer, footprint.type_reads())?;
    writer.tag(match footprint.opacity() {
        | Opacity::Transparent => Tag(0),
        | Opacity::Opaque => Tag(1),
    });
    writer.tag(match footprint.hole() {
        | HoleMark::Filled => Tag(0),
        | HoleMark::Hole => Tag(1),
    });
    Ok(())
}

/// Read a footprint.
///
/// # Specification
/// trivial.
fn read_footprint(reader: &mut Reader<'_>) -> Result<Footprint, CodecError>
{
    let reads = read_references(reader)?;
    let type_reads = read_references(reader)?;
    let opacity = reader.tag()?;
    let opacity = match opacity.0 {
        | 0 => Opacity::Transparent,
        | 1 => Opacity::Opaque,
        | _ => return Err(CodecError::Corrupt),
    };
    let hole = reader.tag()?;
    let hole = match hole.0 {
        | 0 => HoleMark::Filled,
        | 1 => HoleMark::Hole,
        | _ => return Err(CodecError::Corrupt),
    };
    Ok(Footprint::from_parts(reads, type_reads, opacity, hole))
}

/// Write a site.
///
/// # Specification
/// trivial.
fn write_site<Out>(
    writer: &mut Writer<'_, Out>,
    site: Site,
) -> Result<(), CodecError>
where
    Out: Sink,
{
    match site {
        | Site::Node(index) => {
            writer.tag(Tag(0));
            write_index(writer, index)?;
        },
        | Site::Unreached => writer.tag(Tag(1)),
    }
    Ok(())
}

/// Read a site.
///
/// # Specification
/// trivial.
fn read_site(reader: &mut Reader<'_>) -> Result<Site, CodecError>
{
    let tag = reader.tag()?;
    match tag.0 {
        | 0 => {
            let index = read_index(reader)?;
            Ok(Site::Node(index))
        },
        | 1 => Ok(Site::Unreached),
        | _ => Err(CodecError::Corrupt),
    }
}

/// The tags of the unadmitted formers, in declaration order.
const FORMERS: [UnadmittedFormer; 15] = [
    UnadmittedFormer::Pair,
    UnadmittedFormer::Injection,
    UnadmittedFormer::ValueLift,
    UnadmittedFormer::NumericLiteral,
    UnadmittedFormer::Case,
    UnadmittedFormer::NumericAtom,
    UnadmittedFormer::Product,
    UnadmittedFormer::Sum,
    UnadmittedFormer::TypeLift,
    UnadmittedFormer::Abstract,
    UnadmittedFormer::SortParameter,
    UnadmittedFormer::TopUniverse,
    UnadmittedFormer::StaticPi,
    UnadmittedFormer::StaticLambda,
    UnadmittedFormer::StaticApplication,
];

/// The shapes a rule can require, in declaration order.
const SHAPES: [ExpectedShape; 3] = [
    ExpectedShape::Thunk,
    ExpectedShape::Returner,
    ExpectedShape::Arrow,
];

/// Write the position of `wanted` in `table` as a tag.
///
/// # Specification
/// - fails: [`CodecError::Unrepresentable`] when `wanted` is not in `table`,
///   which the exhaustive tables rule out.
/// - panics: none.
fn write_listed<Out, Entry>(
    writer: &mut Writer<'_, Out>,
    table: &[Entry],
    wanted: &Entry,
) -> Result<(), CodecError>
where
    Out: Sink,
    Entry: PartialEq,
{
    let position = table
        .iter()
        .position(|entry| entry == wanted)
        .ok_or(CodecError::Unrepresentable)?;
    let tag = u8::try_from(position).map_err(|_overflow| CodecError::Unrepresentable)?;
    writer.tag(Tag(tag));
    Ok(())
}

/// Read a tag naming an entry of `table`.
///
/// # Specification
/// trivial.
fn read_listed<Entry>(
    reader: &mut Reader<'_>,
    table: &[Entry],
) -> Result<Entry, CodecError>
where
    Entry: Copy,
{
    let tag = reader.tag()?;
    table
        .get(usize::from(tag.0))
        .copied()
        .ok_or(CodecError::Corrupt)
}

/// Write a refusal.
///
/// # Specification
/// trivial.
fn write_refusal<Out>(
    writer: &mut Writer<'_, Out>,
    refusal: &Refusal,
) -> Result<(), CodecError>
where
    Out: Sink,
{
    match *refusal {
        | Refusal::TypeMismatch {
            at,
            ref synthesised,
            ref expected,
        } => {
            writer.tag(Tag(0));
            write_site(writer, at)?;
            write_type(writer, synthesised)?;
            write_type(writer, expected)?;
        },
        | Refusal::ShapeMismatch {
            at,
            wanted,
            ref found,
        } => {
            writer.tag(Tag(1));
            write_site(writer, at)?;
            write_listed(writer, &SHAPES, &wanted)?;
            write_type(writer, found)?;
        },
        | Refusal::NotSynthesisable { form } => {
            writer.tag(Tag(2));
            match form {
                | Form::Thunk(site) => {
                    writer.tag(Tag(0));
                    write_site(writer, site)?;
                },
                | Form::Lambda(site) => {
                    writer.tag(Tag(1));
                    write_site(writer, site)?;
                },
                | Form::Return(site) => {
                    writer.tag(Tag(2));
                    write_site(writer, site)?;
                },
                | Form::Hole => writer.tag(Tag(3)),
            }
        },
        | Refusal::UnknownConstant { at, ref constant } => {
            writer.tag(Tag(3));
            write_site(writer, at)?;
            write_reference(writer, constant)?;
        },
        | Refusal::OutOfFragment { at, former } => {
            writer.tag(Tag(4));
            write_site(writer, at)?;
            write_listed(writer, &FORMERS, &former)?;
        },
        | Refusal::UnboundIndex {
            at,
            zone,
            index,
            depth,
        } => {
            writer.tag(Tag(5));
            write_site(writer, at)?;
            writer.tag(match zone {
                | Zone::Intuitionistic => Tag(0),
                | Zone::Linear => Tag(1),
            });
            writer.word(Word(u64::from(u32::from(index))));
            let depth = word_of(Count(usize::from(depth)))?;
            writer.word(depth);
        },
        | Refusal::BudgetExceeded { budget } => {
            writer.tag(Tag(6));
            let budget = word_of(Count(usize::from(budget)))?;
            writer.word(budget);
        },
        | Refusal::DanglingNode { at } => {
            writer.tag(Tag(7));
            write_site(writer, at)?;
        },
        | Refusal::AdmissionOrder => writer.tag(Tag(8)),
        | Refusal::MachineInvariant => writer.tag(Tag(9)),
        | Refusal::SortMismatch {
            at,
            ref synthesised,
            ref expected,
        } => {
            writer.tag(Tag(10));
            write_site(writer, at)?;
            write_type(writer, synthesised)?;
            write_type(writer, expected)?;
        },
        | Refusal::LevelMismatch {
            at,
            ref synthesised,
            ref expected,
        } => {
            writer.tag(Tag(11));
            write_site(writer, at)?;
            write_type(writer, synthesised)?;
            write_type(writer, expected)?;
        },
        | Refusal::DependentBind {
            at,
            ref synthesised,
        } => {
            writer.tag(Tag(12));
            write_site(writer, at)?;
            write_type(writer, synthesised)?;
        },
        | Refusal::Undecided { at } => {
            writer.tag(Tag(13));
            write_site(writer, at)?;
        },
    }
    Ok(())
}

/// Read a refusal.
///
/// # Specification
/// trivial.
fn read_refusal(reader: &mut Reader<'_>) -> Result<Refusal, CodecError>
{
    let tag = reader.tag()?;
    let refusal = match tag.0 {
        | 0 => {
            let at = read_site(reader)?;
            let synthesised = read_type(reader)?;
            let expected = read_type(reader)?;
            Refusal::TypeMismatch {
                at,
                synthesised,
                expected,
            }
        },
        | 1 => {
            let at = read_site(reader)?;
            let wanted = read_listed(reader, &SHAPES)?;
            let found = read_type(reader)?;
            Refusal::ShapeMismatch { at, wanted, found }
        },
        | 2 => {
            let form = reader.tag()?;
            let form = match form.0 {
                | 0 => {
                    let site = read_site(reader)?;
                    Form::Thunk(site)
                },
                | 1 => {
                    let site = read_site(reader)?;
                    Form::Lambda(site)
                },
                | 2 => {
                    let site = read_site(reader)?;
                    Form::Return(site)
                },
                | 3 => Form::Hole,
                | _ => return Err(CodecError::Corrupt),
            };
            Refusal::NotSynthesisable { form }
        },
        | 3 => {
            let at = read_site(reader)?;
            let constant = read_reference(reader)?;
            Refusal::UnknownConstant { at, constant }
        },
        | 4 => {
            let at = read_site(reader)?;
            let former = read_listed(reader, &FORMERS)?;
            Refusal::OutOfFragment { at, former }
        },
        | 5 => {
            let at = read_site(reader)?;
            let zone = reader.tag()?;
            let zone = match zone.0 {
                | 0 => Zone::Intuitionistic,
                | 1 => Zone::Linear,
                | _ => return Err(CodecError::Corrupt),
            };
            let index = reader.word()?;
            let index = u32::try_from(index.0).map_err(|_overflow| CodecError::Corrupt)?;
            let depth = reader.count()?;
            Refusal::UnboundIndex {
                at,
                zone,
                index: DeBruijnIndex::from(index),
                depth: BinderDepth::from(depth.0),
            }
        },
        | 6 => {
            let budget = reader.count()?;
            Refusal::BudgetExceeded {
                budget: CheckBudget::from(budget.0),
            }
        },
        | 7 => {
            let at = read_site(reader)?;
            Refusal::DanglingNode { at }
        },
        | 8 => Refusal::AdmissionOrder,
        | 9 => Refusal::MachineInvariant,
        | 10 => {
            let at = read_site(reader)?;
            let synthesised = read_type(reader)?;
            let expected = read_type(reader)?;
            Refusal::SortMismatch {
                at,
                synthesised,
                expected,
            }
        },
        | 11 => {
            let at = read_site(reader)?;
            let synthesised = read_type(reader)?;
            let expected = read_type(reader)?;
            Refusal::LevelMismatch {
                at,
                synthesised,
                expected,
            }
        },
        | 12 => {
            let at = read_site(reader)?;
            let synthesised = read_type(reader)?;
            Refusal::DependentBind { at, synthesised }
        },
        | 13 => {
            let at = read_site(reader)?;
            Refusal::Undecided { at }
        },
        | _ => return Err(CodecError::Corrupt),
    };
    Ok(refusal)
}

/// Write a typing.
///
/// # Specification
/// trivial.
fn write_typing<Out>(
    writer: &mut Writer<'_, Out>,
    typing: &Typing,
) -> Result<(), CodecError>
where
    Out: Sink,
{
    match *typing {
        | Typing::Checked { conversions } => {
            writer.tag(Tag(0));
            writer.count(Count(usize::from(conversions)))?;
        },
        | Typing::Synthesised {
            ref produced,
            conversions,
        } => {
            writer.tag(Tag(1));
            write_type(writer, produced)?;
            writer.count(Count(usize::from(conversions)))?;
        },
        | Typing::Owed => writer.tag(Tag(2)),
        | Typing::Refused(ref refusal) => {
            writer.tag(Tag(3));
            write_refusal(writer, refusal)?;
        },
    }
    Ok(())
}

/// Read a typing.
///
/// # Specification
/// trivial.
fn read_typing(reader: &mut Reader<'_>) -> Result<Typing, CodecError>
{
    let tag = reader.tag()?;
    match tag.0 {
        | 0 => {
            let conversions = reader.count()?;
            Ok(Typing::Checked {
                conversions: ConversionCount::from(conversions.0),
            })
        },
        | 1 => {
            let produced = read_type(reader)?;
            let conversions = reader.count()?;
            Ok(Typing::Synthesised {
                produced,
                conversions: ConversionCount::from(conversions.0),
            })
        },
        | 2 => Ok(Typing::Owed),
        | 3 => {
            let refusal = read_refusal(reader)?;
            Ok(Typing::Refused(refusal))
        },
        | _ => Err(CodecError::Corrupt),
    }
}

/// Write an answer.
///
/// # Specification
/// trivial.
fn write_answer<Out>(
    writer: &mut Writer<'_, Out>,
    answer: &Answer,
) -> Result<(), CodecError>
where
    Out: Sink,
{
    match *answer {
        | Answer::Untyped => writer.tag(Tag(0)),
        | Answer::Typed(ref ty) => {
            writer.tag(Tag(1));
            write_type(writer, ty)?;
        },
    }
    Ok(())
}

/// Read an answer.
///
/// # Specification
/// trivial.
fn read_answer(reader: &mut Reader<'_>) -> Result<Answer, CodecError>
{
    let tag = reader.tag()?;
    match tag.0 {
        | 0 => Ok(Answer::Untyped),
        | 1 => {
            let ty = read_type(reader)?;
            Ok(Answer::Typed(ty))
        },
        | _ => Err(CodecError::Corrupt),
    }
}

/// Write one item's checkpoint.
///
/// # Specification
/// trivial.
fn write_checkpoint<Out>(
    writer: &mut Writer<'_, Out>,
    checkpoint: &ItemCheckpoint,
) -> Result<(), CodecError>
where
    Out: Sink,
{
    write_item_content_with(writer, checkpoint.content())?;
    write_footprint(writer, checkpoint.footprint())?;
    writer.count(Count(checkpoint.support().len()))?;
    for answered in checkpoint.support() {
        write_reference(writer, answered.reference())?;
        write_answer(writer, answered.answer())?;
    }
    write_typing(writer, checkpoint.typing())
}

/// Read one item's checkpoint.
///
/// # Specification
/// trivial.
fn read_checkpoint(reader: &mut Reader<'_>) -> Result<ItemCheckpoint, CodecError>
{
    let content = read_item_content(reader)?;
    let footprint = read_footprint(reader)?;
    let count = reader.count()?;
    let mut support = Vec::new();
    for _ in 0 .. count.0 {
        let reference = read_reference(reader)?;
        let answer = read_answer(reader)?;
        support.push(Answered::new(reference, answer));
    }
    let typing = read_typing(reader)?;
    Ok(ItemCheckpoint::new(content, footprint, support, typing))
}

/// The canonical bytes of a checkpoint set.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the magic, the budget, then each item's content, footprint,
///   support and typing, in order.
/// - fails: [`CodecError::Unsupported`] naming the first unresolved node met.
/// - panics: none.
pub fn encode_checkpoints(checkpoints: &Checkpoints) -> Result<CheckpointBytes, CodecError>
{
    let mut bytes = CheckpointBytes::default();
    let mut writer = Writer { sink: &mut bytes };
    writer.sink.put(Bytes(CHECKPOINTS_MAGIC));
    let budget = word_of(Count(usize::from(checkpoints.budget())))?;
    writer.word(budget);
    writer.count(Count(checkpoints.items().len()))?;
    for checkpoint in checkpoints.items() {
        write_checkpoint(&mut writer, checkpoint)?;
    }
    Ok(bytes)
}

/// The checkpoint set `bytes` spell.
///
/// # Specification
/// - requires: nothing — any bytes are admissible input.
/// - ensures: on success the one checkpoint set whose canonical bytes are
///   exactly `bytes`.
/// - fails: [`CodecError::Corrupt`] for truncated, malformed or trailing bytes;
///   [`CodecError::LevelOffsetTooLarge`] for an offset at the cap;
///   [`CodecError::NonCanonical`] for a payload that parses but is not the
///   canonical spelling of what it parses to.
/// - panics: none.
pub fn decode_checkpoints(bytes: Bytes<'_>) -> Result<Checkpoints, CodecError>
{
    let mut reader = Reader {
        bytes: bytes.0,
        cursor: 0,
    };
    let magic = reader.take(Count(CHECKPOINTS_MAGIC.len()))?;
    if magic.0 != CHECKPOINTS_MAGIC {
        return Err(CodecError::Corrupt);
    }
    let budget = reader.count()?;
    let count = reader.count()?;
    let mut items = Vec::new();
    for _ in 0 .. count.0 {
        let checkpoint = read_checkpoint(&mut reader)?;
        items.push(checkpoint);
    }
    reader.finish()?;
    let checkpoints = Checkpoints::new(CheckBudget::from(budget.0), items);
    let canonical = encode_checkpoints(&checkpoints)?;
    if canonical.0.as_slice() == bytes.0 {
        Ok(checkpoints)
    }
    else {
        Err(CodecError::NonCanonical)
    }
}

/// Write the canonical program bytes an address is computed over.
///
/// # Specification
/// - requires: `contents` are a program's items' contents, in order.
/// - ensures: the magic, the count, then each item's content.
/// - fails: [`CodecError::Unsupported`] naming the first unresolved node met.
/// - panics: none.
pub fn write_program<Out>(
    sink: &mut Out,
    contents: &[ItemContent],
) -> Result<(), CodecError>
where
    Out: Sink,
{
    let mut writer = Writer { sink };
    writer.sink.put(Bytes(PROGRAM_MAGIC));
    writer.count(Count(contents.len()))?;
    for content in contents {
        write_item_content_with(&mut writer, content)?;
    }
    Ok(())
}
